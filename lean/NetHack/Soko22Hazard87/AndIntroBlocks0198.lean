import NetHack.Soko22Hazard87.AndIntroBlocks0197
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro49500 (p : Pattern) (ha : d122779 p = 1) (hb : d169863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122770 q = 1) (hb : d169854 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122770, d169854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49498 q ha hb
    | true =>
      simp only [d122770, d169854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49455 q ha hb
  have h2 (q : Pattern) (ha : d122771 q = 1) (hb : d169855 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122771, d169855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122771, d169855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122772 q = 1) (hb : d169856 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122772, d169856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122772, d169856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122774 q = 1) (hb : d169858 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122774, d169858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49455 q ha hb
    | true =>
      simp only [d122774, d169858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49499 q ha hb
  have h5 (q : Pattern) (ha : d122775 q = 1) (hb : d169859 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122775, d169859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122775, d169859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122776 q = 1) (hb : d169860 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122776, d169860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122776, d169860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122777 q = 1) (hb : d169861 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122777, d169861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122777, d169861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122705 q = 1) (hb : d169791 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122705, d169791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49455 q ha hb
    | true =>
      simp only [d122705, d169791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49485 q ha hb
  have h9 (q : Pattern) (ha : d122706 q = 1) (hb : d169792 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122706, d169792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122706, d169792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122707 q = 1) (hb : d169793 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122707, d169793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122707, d169793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122708 q = 1) (hb : d169794 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122708, d169794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49485 q ha hb
    | true =>
      simp only [d122708, d169794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q hb ha
  have h12 (q : Pattern) (ha : d122709 q = 1) (hb : d169795 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122709, d169795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122709, d169795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122710 q = 1) (hb : d169796 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122710, d169796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122710, d169796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122711 q = 1) (hb : d169797 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122711, d169797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122711, d169797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122778 q = 1) (hb : d169862 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122778, d169862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122778, d169862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122779 q = 1) (hb : d169863 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122779, d169863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122779, d169863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro49501 (p : Pattern) (ha : d122785 p = 1) (hb : d169869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122780 q = 1) (hb : d169864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122780, d169864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49500 q ha hb
    | true =>
      simp only [d122780, d169864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122781 q = 1) (hb : d169865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122781, d169865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122781, d169865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122715 q = 1) (hb : d169801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122715, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49486 q ha hb
    | true =>
      simp only [d122715, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122716 q = 1) (hb : d169802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122716, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122716, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122782 q = 1) (hb : d169866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122782, d169866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122782, d169866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122783 q = 1) (hb : d169867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122783, d169867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122783, d169867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122784 q = 1) (hb : d169868 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122784, d169868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122784, d169868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122785 q = 1) (hb : d169869 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122785, d169869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122785, d169869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49502 (p : Pattern) (ha : d122791 p = 1) (hb : d169875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122715 q = 1) (hb : d169801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122715, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49486 q ha hb
    | true =>
      simp only [d122715, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122716 q = 1) (hb : d169802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122716, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122716, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122788 q = 1) (hb : d169872 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122788, d169872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122788, d169872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122789 q = 1) (hb : d169873 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122789, d169873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122789, d169873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122790 q = 1) (hb : d169874 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122790, d169874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122790, d169874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122791 q = 1) (hb : d169875 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122791, d169875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122791, d169875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49503 (p : Pattern) (ha : d122797 p = 1) (hb : d169881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122752 q = 1) (hb : d169838 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122752, d169838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49494 q ha hb
    | true =>
      simp only [d122752, d169838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49495 q ha hb
  have h2 (q : Pattern) (ha : d122753 q = 1) (hb : d169839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122753, d169839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122753, d169839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122754 q = 1) (hb : d169840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122754, d169840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122754, d169840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122755 q = 1) (hb : d169841 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122755, d169841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122755, d169841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122762 q = 1) (hb : d169848 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122762, d169848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49496 q ha hb
    | true =>
      simp only [d122762, d169848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49497 q ha hb
  have h6 (q : Pattern) (ha : d122763 q = 1) (hb : d169849 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122763, d169849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122763, d169849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122764 q = 1) (hb : d169850 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122764, d169850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122764, d169850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122786 q = 1) (hb : d169870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122786, d169870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49501 q ha hb
    | true =>
      simp only [d122786, d169870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49488 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122729 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122787 q = 1) (hb : d169871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122787, d169871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122787, d169871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d122792 q = 1) (hb : d169876 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122792, d169876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49502 q ha hb
    | true =>
      simp only [d122792, d169876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122793 q = 1) (hb : d169877 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122793, d169877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122793, d169877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122794 q = 1) (hb : d169878 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122794, d169878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122794, d169878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122795 q = 1) (hb : d169879 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122795, d169879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122795, d169879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122796 q = 1) (hb : d169880 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122796, d169880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122796, d169880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122797 q = 1) (hb : d169881 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122797, d169881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122797, d169881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro49504 (p : Pattern) (ha : d122798 p = 1) (hb : d169882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122715 q = 1) (hb : d169801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122715, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49486 q ha hb
    | true =>
      simp only [d122715, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122716 q = 1) (hb : d169802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122716, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122716, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122719 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49487 q ha hb
    | true =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122720 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122721 q = 1) (hb : d169807 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122721, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122721, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122722 q = 1) (hb : d169808 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122722, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122722, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122748 q = 1) (hb : d169834 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122748, d169834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122748, d169834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122798 q = 1) (hb : d169882 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122798, d169882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122798, d169882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49505 (p : Pattern) (ha : d122799 p = 1) (hb : d169883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122719 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49487 q ha hb
    | true =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122720 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122725 q = 1) (hb : d169811 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122725, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122725, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122726 q = 1) (hb : d169812 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122726, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122726, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122750 q = 1) (hb : d169836 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122750, d169836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122750, d169836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122799 q = 1) (hb : d169883 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122799, d169883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122799, d169883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49506 (p : Pattern) (ha : d122804 p = 1) (hb : d169888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122715 q = 1) (hb : d169801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122715, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49486 q ha hb
    | true =>
      simp only [d122715, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122716 q = 1) (hb : d169802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122716, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122716, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122719 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49487 q ha hb
    | true =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122720 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122721 q = 1) (hb : d169807 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122721, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122721, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122756 q = 1) (hb : d169842 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122756, d169842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122756, d169842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122757 q = 1) (hb : d169843 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122757, d169843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122757, d169843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122804 q = 1) (hb : d169888 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122804, d169888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122804, d169888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49507 (p : Pattern) (ha : d122805 p = 1) (hb : d169889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122719 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49487 q ha hb
    | true =>
      simp only [d122719, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122720 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122720, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122725 q = 1) (hb : d169811 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122725, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122725, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122759 q = 1) (hb : d169845 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122759, d169845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122759, d169845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122760 q = 1) (hb : d169846 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122760, d169846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122760, d169846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122805 q = 1) (hb : d169889 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122805, d169889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122805, d169889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49508 (p : Pattern) (ha : d122809 p = 1) (hb : d169893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122780 q = 1) (hb : d169864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122780, d169864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49500 q ha hb
    | true =>
      simp only [d122780, d169864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122781 q = 1) (hb : d169865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122781, d169865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122781, d169865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122715 q = 1) (hb : d169801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122715, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49486 q ha hb
    | true =>
      simp only [d122715, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122716 q = 1) (hb : d169802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122716, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122716, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122782 q = 1) (hb : d169866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122782, d169866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122782, d169866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122783 q = 1) (hb : d169867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122783, d169867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122783, d169867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122784 q = 1) (hb : d169868 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122784, d169868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122784, d169868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122809 q = 1) (hb : d169893 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122809, d169893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122809, d169893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49509 (p : Pattern) (ha : d122812 p = 1) (hb : d169896 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122715 q = 1) (hb : d169801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122715, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49486 q ha hb
    | true =>
      simp only [d122715, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122716 q = 1) (hb : d169802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122716, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122716, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122788 q = 1) (hb : d169872 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122788, d169872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122788, d169872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122789 q = 1) (hb : d169873 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122789, d169873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122789, d169873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122790 q = 1) (hb : d169874 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122790, d169874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122790, d169874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122812 q = 1) (hb : d169896 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122812, d169896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122812, d169896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49510 (p : Pattern) (ha : d122818 p = 1) (hb : d169902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122752 q = 1) (hb : d169838 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122752, d169838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49494 q ha hb
    | true =>
      simp only [d122752, d169838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49495 q ha hb
  have h2 (q : Pattern) (ha : d122753 q = 1) (hb : d169839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122753, d169839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122753, d169839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122754 q = 1) (hb : d169840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122754, d169840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122754, d169840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122755 q = 1) (hb : d169841 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122755, d169841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122755, d169841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122762 q = 1) (hb : d169848 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122762, d169848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49496 q ha hb
    | true =>
      simp only [d122762, d169848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49497 q ha hb
  have h6 (q : Pattern) (ha : d122763 q = 1) (hb : d169849 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122763, d169849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122763, d169849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122764 q = 1) (hb : d169850 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122764, d169850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122764, d169850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122786 q = 1) (hb : d169870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122786, d169870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49501 q ha hb
    | true =>
      simp only [d122786, d169870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49488 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122729 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122787 q = 1) (hb : d169871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122787, d169871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122787, d169871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d122792 q = 1) (hb : d169876 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122792, d169876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49502 q ha hb
    | true =>
      simp only [d122792, d169876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122793 q = 1) (hb : d169877 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122793, d169877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122793, d169877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122794 q = 1) (hb : d169878 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122794, d169878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122794, d169878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122795 q = 1) (hb : d169879 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122795, d169879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122795, d169879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122796 q = 1) (hb : d169880 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122796, d169880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122796, d169880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122800 q = 1) (hb : d169884 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122800, d169884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49504 q ha hb
    | true =>
      simp only [d122800, d169884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49505 q ha hb
  have h17 (q : Pattern) (ha : d122801 q = 1) (hb : d169885 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122801, d169885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122801, d169885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d122802 q = 1) (hb : d169886 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122802, d169886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122802, d169886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d122803 q = 1) (hb : d169887 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122803, d169887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122803, d169887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d122806 q = 1) (hb : d169890 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122806, d169890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49506 q ha hb
    | true =>
      simp only [d122806, d169890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49507 q ha hb
  have h21 (q : Pattern) (ha : d122807 q = 1) (hb : d169891 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122807, d169891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122807, d169891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d122808 q = 1) (hb : d169892 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122808, d169892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d122808, d169892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122810 q = 1) (hb : d169894 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122810, d169894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49508 q ha hb
    | true =>
      simp only [d122810, d169894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49491 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d122739 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d122811 q = 1) (hb : d169895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122811, d169895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d122811, d169895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d122813 q = 1) (hb : d169897 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122813, d169897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49509 q ha hb
    | true =>
      simp only [d122813, d169897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d122814 q = 1) (hb : d169898 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122814, d169898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d122814, d169898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d122815 q = 1) (hb : d169899 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122815, d169899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d122815, d169899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d122816 q = 1) (hb : d169900 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122816, d169900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d122816, d169900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d122817 q = 1) (hb : d169901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122817, d169901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d122817, d169901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d122818 q = 1) (hb : d169902 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122818, d169902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122818, d169902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro49511 (p : Pattern) (ha : d122825 p = 1) (hb : d169909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122729 q = 1) (hb : d169815 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122729, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49488 q ha hb
    | true =>
      simp only [d122729, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49489 q ha hb
  have h2 (q : Pattern) (ha : d122730 q = 1) (hb : d169816 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122730, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122730, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122731 q = 1) (hb : d169817 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122731, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122731, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122732 q = 1) (hb : d169818 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122732, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122732, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122733 q = 1) (hb : d169819 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122733, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122733, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122820 q = 1) (hb : d169904 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122820, d169904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49489 q ha hb
    | true =>
      simp only [d122820, d169904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122821 q = 1) (hb : d169905 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122821, d169905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122821, d169905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122822 q = 1) (hb : d169906 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122822, d169906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122822, d169906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122823 q = 1) (hb : d169907 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122823, d169907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122823, d169907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122824 q = 1) (hb : d169908 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122824, d169908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122824, d169908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122825 q = 1) (hb : d169909 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122825, d169909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122825, d169909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49512 (p : Pattern) (ha : d122831 p = 1) (hb : d169915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122820 q = 1) (hb : d169904 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122820, d169904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49489 q ha hb
    | true =>
      simp only [d122820, d169904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122821 q = 1) (hb : d169905 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122821, d169905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122821, d169905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122822 q = 1) (hb : d169906 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122822, d169906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122822, d169906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122823 q = 1) (hb : d169907 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122823, d169907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122823, d169907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122824 q = 1) (hb : d169908 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122824, d169908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122824, d169908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122826 q = 1) (hb : d169910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122826, d169910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49492 q ha hb
    | true =>
      simp only [d122826, d169910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122827 q = 1) (hb : d169911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122827, d169911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122827, d169911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122828 q = 1) (hb : d169912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122828, d169912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122828, d169912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122829 q = 1) (hb : d169913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122829, d169913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122829, d169913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122830 q = 1) (hb : d169914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122830, d169914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122830, d169914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122831 q = 1) (hb : d169915 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122831, d169915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122831, d169915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49513 (p : Pattern) (ha : d122838 p = 1) (hb : d169922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122810 q = 1) (hb : d169894 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122810, d169894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49508 q ha hb
    | true =>
      simp only [d122810, d169894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49491 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122739 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122811 q = 1) (hb : d169895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122811, d169895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122811, d169895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d122813 q = 1) (hb : d169897 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122813, d169897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49509 q ha hb
    | true =>
      simp only [d122813, d169897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122814 q = 1) (hb : d169898 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122814, d169898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122814, d169898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122815 q = 1) (hb : d169899 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122815, d169899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122815, d169899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122836 q = 1) (hb : d169920 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122836, d169920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122836, d169920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122837 q = 1) (hb : d169921 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122837, d169921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122837, d169921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122838 q = 1) (hb : d169922 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122838, d169922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122838, d169922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro49514 (p : Pattern) (ha : d122840 p = 1) (hb : d169924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122826 q = 1) (hb : d169910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122826, d169910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49492 q ha hb
    | true =>
      simp only [d122826, d169910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122827 q = 1) (hb : d169911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122827, d169911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122827, d169911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122828 q = 1) (hb : d169912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122828, d169912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122828, d169912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122829 q = 1) (hb : d169913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122829, d169913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122829, d169913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122830 q = 1) (hb : d169914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122830, d169914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122830, d169914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122840 q = 1) (hb : d169924 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122840, d169924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122840, d169924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49515 (p : Pattern) (ha : d122852 p = 1) (hb : d169932 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21612 q = 1) (hb : d52584 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21612, d52584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21612, d52584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46113 q ha hb
  have h2 (q : Pattern) (ha : d21482 q = 1) (hb : d52511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21482, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46113 q ha hb
    | true =>
      simp only [d21482, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21613 q = 1) (hb : d52585 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21613, d52585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21613, d52585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21483 q = 1) (hb : d52512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21483, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21483, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21614 q = 1) (hb : d52586 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21614, d52586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21614, d52586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21615 q = 1) (hb : d52587 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21615, d52587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21615, d52587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d122846 q = 1) (hb : d169930 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d122846, d169930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d122846, d169930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d21617 q = 1) (hb : d122847 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21617, d122847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21617, d122847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48817 q ha hb
  have h9 (q : Pattern) (ha : d21488 q = 1) (hb : d101177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21488, d101177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48817 q ha hb
    | true =>
      simp only [d21488, d101177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21618 q = 1) (hb : d122848 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21618, d122848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21618, d122848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21489 q = 1) (hb : d101179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21489, d101179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21489, d101179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21619 q = 1) (hb : d122849 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21619, d122849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21619, d122849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21620 q = 1) (hb : d122850 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21620, d122850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21620, d122850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d122851 q = 1) (hb : d169931 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d122851, d169931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d122851, d169931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122852 q = 1) (hb : d169932 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122852, d169932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122852, d169932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49516 (p : Pattern) (ha : d122856 p = 1) (hb : d169936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21314 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21314, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21314, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46115 q ha hb
  have h2 (q : Pattern) (ha : d21189 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46115 q ha hb
    | true =>
      simp only [d21189, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21315 q = 1) (hb : d113215 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21315, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21315, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21190 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21190, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21316 q = 1) (hb : d113216 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21316, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21316, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21317 q = 1) (hb : d113217 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21317, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21317, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d122636 q = 1) (hb : d169723 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d122636, d169723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d122636, d169723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h9 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d972 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d973 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d974 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d980 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d980, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d122856 q = 1) (hb : d169936 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122856, d169936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122856, d169936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro49517 (p : Pattern) (ha : d122861 p = 1) (hb : d169941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21071 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21071, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
  have h2 (q : Pattern) (ha : d20990 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46036 q ha hb
    | true =>
      simp only [d20990, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21072 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21072, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20991 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20991, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21073 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21073, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21074 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21074, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d122464 q = 1) (hb : d169552 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d122464, d169552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d122464, d169552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h9 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d972 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d973 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d974 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d980 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d980, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d122861 q = 1) (hb : d169941 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122861, d169941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122861, d169941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro49518 (p : Pattern) (ha : d122870 p = 1) (hb : d169950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122853 q = 1) (hb : d169933 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122853, d169933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49515 q ha hb
    | true =>
      simp only [d122853, d169933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49472 q ha hb
  have h2 (q : Pattern) (ha : d122854 q = 1) (hb : d169934 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122854, d169934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122854, d169934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122855 q = 1) (hb : d169935 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122855, d169935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122855, d169935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122857 q = 1) (hb : d169937 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122857, d169937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49472 q ha hb
    | true =>
      simp only [d122857, d169937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49516 q ha hb
  have h5 (q : Pattern) (ha : d122858 q = 1) (hb : d169938 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122858, d169938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122858, d169938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122859 q = 1) (hb : d169939 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122859, d169939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122859, d169939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122860 q = 1) (hb : d169940 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122860, d169940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122860, d169940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122862 q = 1) (hb : d169942 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122862, d169942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49472 q ha hb
    | true =>
      simp only [d122862, d169942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49517 q ha hb
  have h9 (q : Pattern) (ha : d122863 q = 1) (hb : d169943 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122863, d169943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122863, d169943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122864 q = 1) (hb : d169944 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122864, d169944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122864, d169944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122865 q = 1) (hb : d169945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122865, d169945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49517 q ha hb
    | true =>
      simp only [d122865, d169945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q hb ha
  have h12 (q : Pattern) (ha : d122866 q = 1) (hb : d169946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122866, d169946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122866, d169946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122867 q = 1) (hb : d169947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122867, d169947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122867, d169947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122868 q = 1) (hb : d169948 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122868, d169948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122868, d169948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122869 q = 1) (hb : d169949 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122869, d169949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122869, d169949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122870 q = 1) (hb : d169950 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122870, d169950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122870, d169950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro49519 (p : Pattern) (ha : d122875 p = 1) (hb : d169955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122862 q = 1) (hb : d169942 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122862, d169942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49472 q ha hb
    | true =>
      simp only [d122862, d169942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49517 q ha hb
  have h2 (q : Pattern) (ha : d122863 q = 1) (hb : d169943 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122863, d169943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122863, d169943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122864 q = 1) (hb : d169944 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122864, d169944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122864, d169944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122865 q = 1) (hb : d169945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122865, d169945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49517 q ha hb
    | true =>
      simp only [d122865, d169945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q hb ha
  have h5 (q : Pattern) (ha : d122866 q = 1) (hb : d169946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122866, d169946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122866, d169946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122867 q = 1) (hb : d169947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122867, d169947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122867, d169947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122868 q = 1) (hb : d169948 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122868, d169948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122868, d169948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122873 q = 1) (hb : d169953 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122873, d169953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122873, d169953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122874 q = 1) (hb : d169954 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122874, d169954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122874, d169954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122875 q = 1) (hb : d169955 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122875, d169955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d122875, d169955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro49520 (p : Pattern) (ha : d122881 p = 1) (hb : d169961 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122871 q = 1) (hb : d169951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122871, d169951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49518 q ha hb
    | true =>
      simp only [d122871, d169951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122872 q = 1) (hb : d169952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122872, d169952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122872, d169952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122876 q = 1) (hb : d169956 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122876, d169956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49519 q ha hb
    | true =>
      simp only [d122876, d169956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122877 q = 1) (hb : d169957 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122877, d169957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122877, d169957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122878 q = 1) (hb : d169958 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122878, d169958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122878, d169958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122879 q = 1) (hb : d169959 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122879, d169959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122879, d169959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122880 q = 1) (hb : d169960 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122880, d169960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122880, d169960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122881 q = 1) (hb : d169961 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122881, d169961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122881, d169961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49521 (p : Pattern) (ha : d122883 p = 1) (hb : d169963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122865 q = 1) (hb : d169945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122865, d169945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49517 q ha hb
    | true =>
      simp only [d122865, d169945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q hb ha
  have h2 (q : Pattern) (ha : d122866 q = 1) (hb : d169946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122866, d169946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122866, d169946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122867 q = 1) (hb : d169947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122867, d169947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122867, d169947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122873 q = 1) (hb : d169953 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122873, d169953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122873, d169953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122882 q = 1) (hb : d169962 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122882, d169962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122882, d169962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122883 q = 1) (hb : d169963 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122883, d169963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122883, d169963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49522 (p : Pattern) (ha : d122889 p = 1) (hb : d169969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122876 q = 1) (hb : d169956 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122876, d169956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49519 q ha hb
    | true =>
      simp only [d122876, d169956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122877 q = 1) (hb : d169957 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122877, d169957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122877, d169957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122884 q = 1) (hb : d169964 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122884, d169964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49521 q ha hb
    | true =>
      simp only [d122884, d169964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122885 q = 1) (hb : d169965 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122885, d169965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122885, d169965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122886 q = 1) (hb : d169966 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122886, d169966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122886, d169966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122887 q = 1) (hb : d169967 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122887, d169967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122887, d169967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122888 q = 1) (hb : d169968 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122888, d169968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122888, d169968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122889 q = 1) (hb : d169969 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122889, d169969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122889, d169969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49523 (p : Pattern) (ha : d122900 p = 1) (hb : d169975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122876 q = 1) (hb : d169956 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122876, d169956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49519 q ha hb
    | true =>
      simp only [d122876, d169956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122877 q = 1) (hb : d169957 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122877, d169957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122877, d169957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122897 q = 1) (hb : d169972 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122897, d169972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122897, d169972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122898 q = 1) (hb : d169973 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122898, d169973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122898, d169973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122899 q = 1) (hb : d169974 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122899, d169974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122899, d169974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122900 q = 1) (hb : d169975 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122900, d169975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122900, d169975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49524 (p : Pattern) (ha : d122906 p = 1) (hb : d169981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122890 q = 1) (hb : d169970 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122890, d169970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49520 q ha hb
    | true =>
      simp only [d122890, d169970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49522 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122895 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122896 q = 1) (hb : d169971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122896, d169971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122896, d169971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d122901 q = 1) (hb : d169976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122901, d169976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49523 q ha hb
    | true =>
      simp only [d122901, d169976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122902 q = 1) (hb : d169977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122902, d169977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122902, d169977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122903 q = 1) (hb : d169978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122903, d169978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122903, d169978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122904 q = 1) (hb : d169979 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122904, d169979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122904, d169979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122905 q = 1) (hb : d169980 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122905, d169980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122905, d169980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122906 q = 1) (hb : d169981 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122906, d169981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122906, d169981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro49525 (p : Pattern) (ha : d122894 p = 1) (hb : d169986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122884 q = 1) (hb : d169964 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122884, d169964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49521 q ha hb
    | true =>
      simp only [d122884, d169964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122885 q = 1) (hb : d169965 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122885, d169965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122885, d169965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122891 q = 1) (hb : d169983 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122891, d169983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122891, d169983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122892 q = 1) (hb : d169984 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122892, d169984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122892, d169984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122893 q = 1) (hb : d169985 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122893, d169985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122893, d169985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122894 q = 1) (hb : d169986 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122894, d169986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122894, d169986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49526 (p : Pattern) (ha : d122913 p = 1) (hb : d169992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122908 q = 1) (hb : d169987 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122908, d169987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49525 q ha hb
    | true =>
      simp only [d122908, d169987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122909 q = 1) (hb : d169988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122909, d169988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122909, d169988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122910 q = 1) (hb : d169989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122910, d169989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122910, d169989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122911 q = 1) (hb : d169990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122911, d169990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122911, d169990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122912 q = 1) (hb : d169991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122912, d169991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122912, d169991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122913 q = 1) (hb : d169992 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122913, d169992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122913, d169992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49527 (p : Pattern) (ha : d122919 p = 1) (hb : d169998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122735 q = 1) (hb : d169821 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122735, d169821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122735, d169821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49490 q ha hb
  have h2 (q : Pattern) (ha : d122736 q = 1) (hb : d169822 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122736, d169822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122736, d169822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122745 q = 1) (hb : d169831 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122745, d169831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49490 q ha hb
    | true =>
      simp only [d122745, d169831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49493 q ha hb
  have h4 (q : Pattern) (ha : d122746 q = 1) (hb : d169832 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122746, d169832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122746, d169832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122747 q = 1) (hb : d169833 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122747, d169833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122747, d169833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122819 q = 1) (hb : d169903 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122819, d169903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49503 q ha hb
    | true =>
      simp only [d122819, d169903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49510 q ha hb
  have h7 (q : Pattern) (ha : d122832 q = 1) (hb : d169916 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122832, d169916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49511 q ha hb
    | true =>
      simp only [d122832, d169916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49512 q ha hb
  have h8 (q : Pattern) (ha : d122833 q = 1) (hb : d169917 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122833, d169917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122833, d169917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122834 q = 1) (hb : d169918 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122834, d169918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122834, d169918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122835 q = 1) (hb : d169919 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122835, d169919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122835, d169919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122839 q = 1) (hb : d169923 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122839, d169923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122839, d169923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49513 q ha hb
  have h12 (q : Pattern) (ha : d122841 q = 1) (hb : d169925 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122841, d169925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122841, d169925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49514 q ha hb
  have h13 (q : Pattern) (ha : d122842 q = 1) (hb : d169926 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122842, d169926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122842, d169926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122843 q = 1) (hb : d169927 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122843, d169927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122843, d169927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122844 q = 1) (hb : d169928 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122844, d169928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d122844, d169928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d122845 q = 1) (hb : d169929 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122845, d169929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122845, d169929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122907 q = 1) (hb : d169982 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122907, d169982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122907, d169982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49524 q ha hb
  have h18 (q : Pattern) (ha : d122914 q = 1) (hb : d169993 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122914, d169993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122914, d169993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49526 q ha hb
  have h19 (q : Pattern) (ha : d122915 q = 1) (hb : d169994 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122915, d169994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122915, d169994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d122916 q = 1) (hb : d169995 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122916, d169995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d122916, d169995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d122917 q = 1) (hb : d169996 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122917, d169996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d122917, d169996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d122918 q = 1) (hb : d169997 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122918, d169997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d122918, d169997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122919 q = 1) (hb : d169998 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d122919, d169998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d122919, d169998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro49528 (p : Pattern) (ha : d122925 p = 1) (hb : d170004 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122920 q = 1) (hb : d169999 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d122920, d169999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122920, d169999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49527 q ha hb
  have h2 (q : Pattern) (ha : d122921 q = 1) (hb : d170000 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d122921, d170000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122921, d170000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122922 q = 1) (hb : d170001 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d122922, d170001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122922, d170001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122923 q = 1) (hb : d170002 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d122923, d170002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122923, d170002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122924 q = 1) (hb : d170003 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d122924, d170003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122924, d170003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122925 q = 1) (hb : d170004 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d122925, d170004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122925, d170004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49529 (p : Pattern) (ha : d122932 p = 1) (hb : d170009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21737 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21737, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46151 q ha hb
    | true =>
      simp only [d21737, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21738 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21738, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21738, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21739 q = 1) (hb : d52683 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21739, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21739, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21740 q = 1) (hb : d52684 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21740, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21740, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122928 q = 1) (hb : d170007 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d122928, d170007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122928, d170007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d21748 q = 1) (hb : d101299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21748, d101299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48843 q ha hb
    | true =>
      simp only [d21748, d101299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21749 q = 1) (hb : d101301 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21749, d101301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21749, d101301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21750 q = 1) (hb : d122929 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21750, d122929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21750, d122929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21751 q = 1) (hb : d122930 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21751, d122930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21751, d122930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d122931 q = 1) (hb : d170008 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d122931, d170008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d122931, d170008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d122932 q = 1) (hb : d170009 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122932, d170009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122932, d170009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49530 (p : Pattern) (ha : d122937 p = 1) (hb : d170011 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21742 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46147 q ha hb
    | true =>
      simp only [d21742, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21743 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21743, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21744 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21744, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21744, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21745 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21745, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21745, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122933 q = 1) (hb : d170010 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d122933, d170010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122933, d170010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d13025 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33439 q ha hb
    | true =>
      simp only [d13025, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13026 q = 1) (hb : d101323 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13026, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13027 q = 1) (hb : d122934 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13027, d122934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13027, d122934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13028 q = 1) (hb : d122935 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13028, d122935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13028, d122935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21760 q = 1) (hb : d122936 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21760, d122936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21760, d122936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d122937 q = 1) (hb : d170011 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d122937, d170011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122937, d170011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro49531 (p : Pattern) (ha : d122955 p = 1) (hb : d170024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122938 q = 1) (hb : d170012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122938, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49529 q ha hb
    | true =>
      simp only [d122938, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49530 q ha hb
  have h2 (q : Pattern) (ha : d122939 q = 1) (hb : d170013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122939, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122939, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122940 q = 1) (hb : d170014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122940, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122940, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122945 q = 1) (hb : d170015 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122945, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49530 q ha hb
    | true =>
      simp only [d122945, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48846 q hb ha
  have h5 (q : Pattern) (ha : d122946 q = 1) (hb : d170016 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122946, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122946, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122947 q = 1) (hb : d170017 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122947, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122947, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122948 q = 1) (hb : d170018 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122948, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122948, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122950 q = 1) (hb : d170019 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122950, d170019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49530 q ha hb
    | true =>
      simp only [d122950, d170019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48847 q hb ha
  have h9 (q : Pattern) (ha : d122951 q = 1) (hb : d170020 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122951, d170020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122951, d170020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122952 q = 1) (hb : d170021 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122952, d170021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122952, d170021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122953 q = 1) (hb : d170022 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122953, d170022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122953, d170022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122954 q = 1) (hb : d170023 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122954, d170023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122954, d170023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122955 q = 1) (hb : d170024 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122955, d170024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d122955, d170024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro49532 (p : Pattern) (ha : d122959 p = 1) (hb : d170028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122950 q = 1) (hb : d170019 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122950, d170019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49530 q ha hb
    | true =>
      simp only [d122950, d170019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48847 q hb ha
  have h2 (q : Pattern) (ha : d122951 q = 1) (hb : d170020 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122951, d170020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122951, d170020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122952 q = 1) (hb : d170021 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122952, d170021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122952, d170021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122953 q = 1) (hb : d170022 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122953, d170022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122953, d170022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122958 q = 1) (hb : d170027 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d122958, d170027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122958, d170027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122959 q = 1) (hb : d170028 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d122959, d170028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122959, d170028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49533 (p : Pattern) (ha : d122965 p = 1) (hb : d170034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122956 q = 1) (hb : d170025 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122956, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49531 q ha hb
    | true =>
      simp only [d122956, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122957 q = 1) (hb : d170026 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122957, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122957, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122960 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49532 q ha hb
    | true =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122961 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122962 q = 1) (hb : d170031 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122962, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122962, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122963 q = 1) (hb : d170032 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122963, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122963, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122964 q = 1) (hb : d170033 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122964, d170033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122964, d170033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122965 q = 1) (hb : d170034 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122965, d170034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122965, d170034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49534 (p : Pattern) (ha : d122969 p = 1) (hb : d170038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122960 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49532 q ha hb
    | true =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122961 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122966 q = 1) (hb : d170035 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122966, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122966, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122967 q = 1) (hb : d170036 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122967, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122967, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122968 q = 1) (hb : d170037 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122968, d170037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122968, d170037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122969 q = 1) (hb : d170038 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122969, d170038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122969, d170038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49535 (p : Pattern) (ha : d122975 p = 1) (hb : d170044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122970 q = 1) (hb : d170039 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122970, d170039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49533 q ha hb
    | true =>
      simp only [d122970, d170039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49534 q ha hb
  have h2 (q : Pattern) (ha : d122971 q = 1) (hb : d170040 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122971, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122971, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122972 q = 1) (hb : d170041 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122972, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122972, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122973 q = 1) (hb : d170042 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122973, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122973, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122974 q = 1) (hb : d170043 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122974, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122974, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122975 q = 1) (hb : d170044 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122975, d170044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122975, d170044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49536 (p : Pattern) (ha : d122978 p = 1) (hb : d170047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122956 q = 1) (hb : d170025 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122956, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49531 q ha hb
    | true =>
      simp only [d122956, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122957 q = 1) (hb : d170026 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122957, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122957, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122960 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49532 q ha hb
    | true =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122961 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122962 q = 1) (hb : d170031 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122962, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122962, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122963 q = 1) (hb : d170032 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122963, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122963, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122964 q = 1) (hb : d170033 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122964, d170033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122964, d170033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122978 q = 1) (hb : d170047 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122978, d170047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122978, d170047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49537 (p : Pattern) (ha : d122979 p = 1) (hb : d170048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122960 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49532 q ha hb
    | true =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122961 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122966 q = 1) (hb : d170035 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122966, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122966, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122967 q = 1) (hb : d170036 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122967, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122967, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122968 q = 1) (hb : d170037 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122968, d170037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122968, d170037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122979 q = 1) (hb : d170048 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122979, d170048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122979, d170048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49538 (p : Pattern) (ha : d122985 p = 1) (hb : d170054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122970 q = 1) (hb : d170039 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122970, d170039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49533 q ha hb
    | true =>
      simp only [d122970, d170039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49534 q ha hb
  have h2 (q : Pattern) (ha : d122971 q = 1) (hb : d170040 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122971, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122971, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122972 q = 1) (hb : d170041 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122972, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122972, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122973 q = 1) (hb : d170042 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122973, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122973, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122974 q = 1) (hb : d170043 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122974, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122974, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122980 q = 1) (hb : d170049 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122980, d170049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49536 q ha hb
    | true =>
      simp only [d122980, d170049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49537 q ha hb
  have h7 (q : Pattern) (ha : d122981 q = 1) (hb : d170050 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122981, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122981, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122982 q = 1) (hb : d170051 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122982, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122982, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122983 q = 1) (hb : d170052 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122983, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122983, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122984 q = 1) (hb : d170053 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122984, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122984, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122985 q = 1) (hb : d170054 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122985, d170054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122985, d170054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49539 (p : Pattern) (ha : d122990 p = 1) (hb : d170059 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122956 q = 1) (hb : d170025 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122956, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49531 q ha hb
    | true =>
      simp only [d122956, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122957 q = 1) (hb : d170026 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122957, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122957, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122960 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49532 q ha hb
    | true =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122961 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122962 q = 1) (hb : d170031 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122962, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122962, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122963 q = 1) (hb : d170032 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122963, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122963, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122989 q = 1) (hb : d170058 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122989, d170058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122989, d170058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122990 q = 1) (hb : d170059 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122990, d170059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122990, d170059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49540 (p : Pattern) (ha : d122992 p = 1) (hb : d170061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122960 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49532 q ha hb
    | true =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122961 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122966 q = 1) (hb : d170035 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122966, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122966, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122967 q = 1) (hb : d170036 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122967, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122967, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122991 q = 1) (hb : d170060 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122991, d170060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122991, d170060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122992 q = 1) (hb : d170061 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122992, d170061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122992, d170061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49541 (p : Pattern) (ha : d122999 p = 1) (hb : d170068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122956 q = 1) (hb : d170025 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122956, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49531 q ha hb
    | true =>
      simp only [d122956, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122957 q = 1) (hb : d170026 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122957, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122957, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122960 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49532 q ha hb
    | true =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122961 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122962 q = 1) (hb : d170031 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122962, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122962, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122997 q = 1) (hb : d170066 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122997, d170066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122997, d170066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122998 q = 1) (hb : d170067 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122998, d170067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122998, d170067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122999 q = 1) (hb : d170068 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d122999, d170068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122999, d170068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49542 (p : Pattern) (ha : d123002 p = 1) (hb : d170071 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122960 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49532 q ha hb
    | true =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122961 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122966 q = 1) (hb : d170035 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122966, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122966, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123000 q = 1) (hb : d170069 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123000, d170069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123000, d170069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123001 q = 1) (hb : d170070 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123001, d170070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123001, d170070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123002 q = 1) (hb : d170071 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123002, d170071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123002, d170071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49543 (p : Pattern) (ha : d123010 p = 1) (hb : d170077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21835 q = 1) (hb : d52791 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21835, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46165 q ha hb
    | true =>
      simp only [d21835, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21836 q = 1) (hb : d52792 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21836, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21836, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21837 q = 1) (hb : d52793 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21837, d52793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21837, d52793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21838 q = 1) (hb : d52794 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21838, d52794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21838, d52794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d123006 q = 1) (hb : d170075 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123006, d170075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123006, d170075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d21841 q = 1) (hb : d101284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21841, d101284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48870 q ha hb
    | true =>
      simp only [d21841, d101284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21842 q = 1) (hb : d101286 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21842, d101286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21842, d101286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21843 q = 1) (hb : d123007 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21843, d123007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21843, d123007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21844 q = 1) (hb : d123008 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21844, d123008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21844, d123008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d123009 q = 1) (hb : d170076 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123009, d170076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d123009, d170076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d123010 q = 1) (hb : d170077 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123010, d170077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123010, d170077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49544 (p : Pattern) (ha : d123015 p = 1) (hb : d170082 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21851 q = 1) (hb : d101335 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21851, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46167 q ha hb
    | true =>
      simp only [d21851, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21852 q = 1) (hb : d101337 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21852, d101337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21852, d101337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21853 q = 1) (hb : d113352 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21853, d113352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21853, d113352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21854 q = 1) (hb : d113353 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21854, d113353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21854, d113353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d123014 q = 1) (hb : d170081 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123014, d170081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123014, d170081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d13025 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33439 q ha hb
    | true =>
      simp only [d13025, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13026 q = 1) (hb : d101323 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13026, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13027 q = 1) (hb : d122934 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13027, d122934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13027, d122934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13028 q = 1) (hb : d122935 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13028, d122935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13028, d122935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21760 q = 1) (hb : d122936 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21760, d122936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21760, d122936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d123015 q = 1) (hb : d170082 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123015, d170082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123015, d170082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro49545 (p : Pattern) (ha : d123021 p = 1) (hb : d170088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123011 q = 1) (hb : d170078 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123011, d170078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49543 q ha hb
    | true =>
      simp only [d123011, d170078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49529 q ha hb
  have h2 (q : Pattern) (ha : d123012 q = 1) (hb : d170079 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123012, d170079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123012, d170079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123013 q = 1) (hb : d170080 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123013, d170080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123013, d170080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123016 q = 1) (hb : d170083 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123016, d170083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49529 q ha hb
    | true =>
      simp only [d123016, d170083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49544 q ha hb
  have h5 (q : Pattern) (ha : d123017 q = 1) (hb : d170084 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123017, d170084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123017, d170084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123018 q = 1) (hb : d170085 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123018, d170085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123018, d170085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123019 q = 1) (hb : d170086 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123019, d170086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123019, d170086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122938 q = 1) (hb : d170012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122938, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49529 q ha hb
    | true =>
      simp only [d122938, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49530 q ha hb
  have h9 (q : Pattern) (ha : d122939 q = 1) (hb : d170013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122939, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122939, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122940 q = 1) (hb : d170014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122940, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122940, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122945 q = 1) (hb : d170015 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122945, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49530 q ha hb
    | true =>
      simp only [d122945, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48846 q hb ha
  have h12 (q : Pattern) (ha : d122946 q = 1) (hb : d170016 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122946, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122946, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122947 q = 1) (hb : d170017 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122947, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122947, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122948 q = 1) (hb : d170018 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122948, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122948, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123020 q = 1) (hb : d170087 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123020, d170087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123020, d170087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123021 q = 1) (hb : d170088 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123021, d170088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123021, d170088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro49546 (p : Pattern) (ha : d123026 p = 1) (hb : d170093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122938 q = 1) (hb : d170012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122938, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49529 q ha hb
    | true =>
      simp only [d122938, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49530 q ha hb
  have h2 (q : Pattern) (ha : d122939 q = 1) (hb : d170013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122939, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122939, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122940 q = 1) (hb : d170014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122940, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122940, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122945 q = 1) (hb : d170015 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122945, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49530 q ha hb
    | true =>
      simp only [d122945, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48846 q hb ha
  have h5 (q : Pattern) (ha : d122946 q = 1) (hb : d170016 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122946, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122946, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122947 q = 1) (hb : d170017 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122947, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122947, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122948 q = 1) (hb : d170018 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122948, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122948, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123024 q = 1) (hb : d170091 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123024, d170091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123024, d170091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123025 q = 1) (hb : d170092 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123025, d170092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123025, d170092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123026 q = 1) (hb : d170093 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123026, d170093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d123026, d170093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro49547 (p : Pattern) (ha : d123032 p = 1) (hb : d170099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123022 q = 1) (hb : d170089 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123022, d170089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49545 q ha hb
    | true =>
      simp only [d123022, d170089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123023 q = 1) (hb : d170090 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123023, d170090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123023, d170090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123027 q = 1) (hb : d170094 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123027, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49546 q ha hb
    | true =>
      simp only [d123027, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123028 q = 1) (hb : d170095 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123028, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123028, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123029 q = 1) (hb : d170096 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123029, d170096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123029, d170096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123030 q = 1) (hb : d170097 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123030, d170097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123030, d170097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123031 q = 1) (hb : d170098 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123031, d170098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123031, d170098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123032 q = 1) (hb : d170099 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123032, d170099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123032, d170099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49548 (p : Pattern) (ha : d123036 p = 1) (hb : d170103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123027 q = 1) (hb : d170094 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123027, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49546 q ha hb
    | true =>
      simp only [d123027, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123028 q = 1) (hb : d170095 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123028, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123028, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122960 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49532 q ha hb
    | true =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122961 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123033 q = 1) (hb : d170100 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123033, d170100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123033, d170100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123034 q = 1) (hb : d170101 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123034, d170101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123034, d170101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123035 q = 1) (hb : d170102 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123035, d170102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123035, d170102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123036 q = 1) (hb : d170103 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123036, d170103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123036, d170103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49549 (p : Pattern) (ha : d123044 p = 1) (hb : d170111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122938 q = 1) (hb : d170012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122938, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49529 q ha hb
    | true =>
      simp only [d122938, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49530 q ha hb
  have h2 (q : Pattern) (ha : d122939 q = 1) (hb : d170013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122939, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122939, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122940 q = 1) (hb : d170014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122940, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122940, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122945 q = 1) (hb : d170015 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d122945, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49530 q ha hb
    | true =>
      simp only [d122945, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48846 q hb ha
  have h5 (q : Pattern) (ha : d122946 q = 1) (hb : d170016 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d122946, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122946, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122947 q = 1) (hb : d170017 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d122947, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122947, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122948 q = 1) (hb : d170018 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d122948, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122948, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123039 q = 1) (hb : d170106 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123039, d170106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49530 q ha hb
    | true =>
      simp only [d123039, d170106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46146 q hb ha
  have h9 (q : Pattern) (ha : d123040 q = 1) (hb : d170107 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123040, d170107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123040, d170107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123041 q = 1) (hb : d170108 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123041, d170108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123041, d170108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123042 q = 1) (hb : d170109 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123042, d170109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123042, d170109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123043 q = 1) (hb : d170110 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123043, d170110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123043, d170110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123044 q = 1) (hb : d170111 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123044, d170111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123044, d170111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro49550 (p : Pattern) (ha : d123050 p = 1) (hb : d170117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123045 q = 1) (hb : d170112 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123045, d170112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49549 q ha hb
    | true =>
      simp only [d123045, d170112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123046 q = 1) (hb : d170113 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123046, d170113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123046, d170113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123047 q = 1) (hb : d170114 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123047, d170114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123047, d170114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123048 q = 1) (hb : d170115 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123048, d170115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123048, d170115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123049 q = 1) (hb : d170116 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123049, d170116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123049, d170116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123050 q = 1) (hb : d170117 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123050, d170117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123050, d170117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49551 (p : Pattern) (ha : d123056 p = 1) (hb : d170123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122993 q = 1) (hb : d170062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122993, d170062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49539 q ha hb
    | true =>
      simp only [d122993, d170062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49540 q ha hb
  have h2 (q : Pattern) (ha : d122994 q = 1) (hb : d170063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122994, d170063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122994, d170063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122995 q = 1) (hb : d170064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122995, d170064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122995, d170064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122996 q = 1) (hb : d170065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122996, d170065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122996, d170065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123003 q = 1) (hb : d170072 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123003, d170072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49541 q ha hb
    | true =>
      simp only [d123003, d170072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49542 q ha hb
  have h6 (q : Pattern) (ha : d123004 q = 1) (hb : d170073 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123004, d170073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123004, d170073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123005 q = 1) (hb : d170074 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123005, d170074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123005, d170074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123037 q = 1) (hb : d170104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123037, d170104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49547 q ha hb
    | true =>
      simp only [d123037, d170104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49548 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122970 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d123038 q = 1) (hb : d170105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123038, d170105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123038, d170105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d123051 q = 1) (hb : d170118 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123051, d170118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49550 q ha hb
    | true =>
      simp only [d123051, d170118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123052 q = 1) (hb : d170119 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123052, d170119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123052, d170119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d123053 q = 1) (hb : d170120 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123053, d170120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123053, d170120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123054 q = 1) (hb : d170121 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123054, d170121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123054, d170121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123055 q = 1) (hb : d170122 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123055, d170122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123055, d170122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123056 q = 1) (hb : d170123 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123056, d170123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123056, d170123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro49552 (p : Pattern) (ha : d123057 p = 1) (hb : d170124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122956 q = 1) (hb : d170025 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122956, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49531 q ha hb
    | true =>
      simp only [d122956, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122957 q = 1) (hb : d170026 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122957, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122957, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122960 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49532 q ha hb
    | true =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122961 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122962 q = 1) (hb : d170031 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122962, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122962, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122963 q = 1) (hb : d170032 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122963, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122963, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122989 q = 1) (hb : d170058 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122989, d170058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122989, d170058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123057 q = 1) (hb : d170124 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123057, d170124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123057, d170124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49553 (p : Pattern) (ha : d123058 p = 1) (hb : d170125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122960 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49532 q ha hb
    | true =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122961 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122966 q = 1) (hb : d170035 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122966, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122966, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122967 q = 1) (hb : d170036 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122967, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122967, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122991 q = 1) (hb : d170060 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122991, d170060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122991, d170060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123058 q = 1) (hb : d170125 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123058, d170125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123058, d170125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49554 (p : Pattern) (ha : d123063 p = 1) (hb : d170130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122956 q = 1) (hb : d170025 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122956, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49531 q ha hb
    | true =>
      simp only [d122956, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122957 q = 1) (hb : d170026 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122957, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122957, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122960 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49532 q ha hb
    | true =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122961 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122962 q = 1) (hb : d170031 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122962, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122962, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122997 q = 1) (hb : d170066 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d122997, d170066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122997, d170066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122998 q = 1) (hb : d170067 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122998, d170067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122998, d170067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123063 q = 1) (hb : d170130 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123063, d170130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123063, d170130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49555 (p : Pattern) (ha : d123064 p = 1) (hb : d170131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122960 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49532 q ha hb
    | true =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122961 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122966 q = 1) (hb : d170035 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d122966, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122966, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123000 q = 1) (hb : d170069 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123000, d170069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123000, d170069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123001 q = 1) (hb : d170070 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123001, d170070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123001, d170070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123064 q = 1) (hb : d170131 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123064, d170131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123064, d170131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49556 (p : Pattern) (ha : d123068 p = 1) (hb : d170135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123022 q = 1) (hb : d170089 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123022, d170089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49545 q ha hb
    | true =>
      simp only [d123022, d170089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123023 q = 1) (hb : d170090 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123023, d170090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123023, d170090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123027 q = 1) (hb : d170094 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123027, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49546 q ha hb
    | true =>
      simp only [d123027, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123028 q = 1) (hb : d170095 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123028, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123028, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123029 q = 1) (hb : d170096 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123029, d170096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123029, d170096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123030 q = 1) (hb : d170097 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123030, d170097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123030, d170097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123031 q = 1) (hb : d170098 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123031, d170098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123031, d170098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123068 q = 1) (hb : d170135 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123068, d170135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123068, d170135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49557 (p : Pattern) (ha : d123069 p = 1) (hb : d170136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123027 q = 1) (hb : d170094 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123027, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49546 q ha hb
    | true =>
      simp only [d123027, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123028 q = 1) (hb : d170095 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123028, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123028, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122960 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49532 q ha hb
    | true =>
      simp only [d122960, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122961 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122961, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123033 q = 1) (hb : d170100 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123033, d170100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123033, d170100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123034 q = 1) (hb : d170101 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123034, d170101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123034, d170101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123035 q = 1) (hb : d170102 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123035, d170102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123035, d170102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123069 q = 1) (hb : d170136 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123069, d170136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123069, d170136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49558 (p : Pattern) (ha : d123072 p = 1) (hb : d170139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123045 q = 1) (hb : d170112 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123045, d170112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49549 q ha hb
    | true =>
      simp only [d123045, d170112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123046 q = 1) (hb : d170113 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123046, d170113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123046, d170113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123047 q = 1) (hb : d170114 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123047, d170114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123047, d170114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123048 q = 1) (hb : d170115 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123048, d170115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123048, d170115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123049 q = 1) (hb : d170116 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123049, d170116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123049, d170116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123072 q = 1) (hb : d170139 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123072, d170139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123072, d170139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49559 (p : Pattern) (ha : d123078 p = 1) (hb : d170145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122993 q = 1) (hb : d170062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122993, d170062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49539 q ha hb
    | true =>
      simp only [d122993, d170062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49540 q ha hb
  have h2 (q : Pattern) (ha : d122994 q = 1) (hb : d170063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122994, d170063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122994, d170063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122995 q = 1) (hb : d170064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122995, d170064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122995, d170064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122996 q = 1) (hb : d170065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122996, d170065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122996, d170065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123003 q = 1) (hb : d170072 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123003, d170072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49541 q ha hb
    | true =>
      simp only [d123003, d170072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49542 q ha hb
  have h6 (q : Pattern) (ha : d123004 q = 1) (hb : d170073 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123004, d170073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123004, d170073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123005 q = 1) (hb : d170074 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123005, d170074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123005, d170074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123037 q = 1) (hb : d170104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123037, d170104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49547 q ha hb
    | true =>
      simp only [d123037, d170104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49548 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122970 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d123038 q = 1) (hb : d170105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123038, d170105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123038, d170105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d123051 q = 1) (hb : d170118 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123051, d170118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49550 q ha hb
    | true =>
      simp only [d123051, d170118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123052 q = 1) (hb : d170119 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123052, d170119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123052, d170119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d123053 q = 1) (hb : d170120 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123053, d170120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123053, d170120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123054 q = 1) (hb : d170121 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123054, d170121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123054, d170121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123055 q = 1) (hb : d170122 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123055, d170122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123055, d170122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123059 q = 1) (hb : d170126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123059, d170126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49552 q ha hb
    | true =>
      simp only [d123059, d170126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49553 q ha hb
  have h17 (q : Pattern) (ha : d123060 q = 1) (hb : d170127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123060, d170127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123060, d170127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d123061 q = 1) (hb : d170128 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123061, d170128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123061, d170128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d123062 q = 1) (hb : d170129 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123062, d170129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123062, d170129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d123065 q = 1) (hb : d170132 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123065, d170132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49554 q ha hb
    | true =>
      simp only [d123065, d170132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49555 q ha hb
  have h21 (q : Pattern) (ha : d123066 q = 1) (hb : d170133 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123066, d170133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123066, d170133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d123067 q = 1) (hb : d170134 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123067, d170134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d123067, d170134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d123070 q = 1) (hb : d170137 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123070, d170137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49556 q ha hb
    | true =>
      simp only [d123070, d170137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49557 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d122980 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d123071 q = 1) (hb : d170138 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123071, d170138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d123071, d170138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d123073 q = 1) (hb : d170140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123073, d170140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49558 q ha hb
    | true =>
      simp only [d123073, d170140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d123074 q = 1) (hb : d170141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123074, d170141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d123074, d170141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d123075 q = 1) (hb : d170142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123075, d170142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d123075, d170142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d123076 q = 1) (hb : d170143 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123076, d170143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d123076, d170143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d123077 q = 1) (hb : d170144 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123077, d170144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d123077, d170144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d123078 q = 1) (hb : d170145 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123078, d170145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123078, d170145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro49560 (p : Pattern) (ha : d123090 p = 1) (hb : d170157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123080 q = 1) (hb : d170147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123080, d170147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49548 q ha hb
    | true =>
      simp only [d123080, d170147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49534 q ha hb
  have h2 (q : Pattern) (ha : d123081 q = 1) (hb : d170148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123081, d170148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123081, d170148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123082 q = 1) (hb : d170149 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123082, d170149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123082, d170149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123083 q = 1) (hb : d170150 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123083, d170150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123083, d170150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123084 q = 1) (hb : d170151 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123084, d170151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123084, d170151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123085 q = 1) (hb : d170152 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123085, d170152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49534 q ha hb
    | true =>
      simp only [d123085, d170152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123086 q = 1) (hb : d170153 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123086, d170153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123086, d170153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123087 q = 1) (hb : d170154 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123087, d170154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123087, d170154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123088 q = 1) (hb : d170155 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123088, d170155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123088, d170155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123089 q = 1) (hb : d170156 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123089, d170156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123089, d170156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123090 q = 1) (hb : d170157 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123090, d170157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123090, d170157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49561 (p : Pattern) (ha : d123096 p = 1) (hb : d170163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123085 q = 1) (hb : d170152 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123085, d170152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49534 q ha hb
    | true =>
      simp only [d123085, d170152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123086 q = 1) (hb : d170153 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123086, d170153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123086, d170153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123087 q = 1) (hb : d170154 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123087, d170154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123087, d170154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123088 q = 1) (hb : d170155 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123088, d170155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123088, d170155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123089 q = 1) (hb : d170156 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123089, d170156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123089, d170156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123091 q = 1) (hb : d170158 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123091, d170158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49537 q ha hb
    | true =>
      simp only [d123091, d170158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123092 q = 1) (hb : d170159 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123092, d170159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123092, d170159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123093 q = 1) (hb : d170160 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123093, d170160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123093, d170160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123094 q = 1) (hb : d170161 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123094, d170161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123094, d170161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123095 q = 1) (hb : d170162 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123095, d170162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123095, d170162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123096 q = 1) (hb : d170163 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123096, d170163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123096, d170163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49562 (p : Pattern) (ha : d123103 p = 1) (hb : d170170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123070 q = 1) (hb : d170137 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123070, d170137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49556 q ha hb
    | true =>
      simp only [d123070, d170137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49557 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122980 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123071 q = 1) (hb : d170138 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123071, d170138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123071, d170138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d123073 q = 1) (hb : d170140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123073, d170140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49558 q ha hb
    | true =>
      simp only [d123073, d170140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123074 q = 1) (hb : d170141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123074, d170141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123074, d170141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123075 q = 1) (hb : d170142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123075, d170142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123075, d170142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123101 q = 1) (hb : d170168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123101, d170168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123101, d170168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123102 q = 1) (hb : d170169 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123102, d170169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123102, d170169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123103 q = 1) (hb : d170170 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123103, d170170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123103, d170170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro49563 (p : Pattern) (ha : d123105 p = 1) (hb : d170172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123091 q = 1) (hb : d170158 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123091, d170158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49537 q ha hb
    | true =>
      simp only [d123091, d170158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123092 q = 1) (hb : d170159 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123092, d170159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123092, d170159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123093 q = 1) (hb : d170160 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123093, d170160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123093, d170160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123094 q = 1) (hb : d170161 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123094, d170161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123094, d170161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123095 q = 1) (hb : d170162 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123095, d170162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123095, d170162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123105 q = 1) (hb : d170172 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123105, d170172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123105, d170172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49564 (p : Pattern) (ha : d123117 p = 1) (hb : d170180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22024 q = 1) (hb : d52864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22024, d52864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22024, d52864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46165 q ha hb
  have h2 (q : Pattern) (ha : d21835 q = 1) (hb : d52791 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21835, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46165 q ha hb
    | true =>
      simp only [d21835, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22025 q = 1) (hb : d52865 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22025, d52865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22025, d52865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21836 q = 1) (hb : d52792 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21836, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21836, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22026 q = 1) (hb : d52866 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22026, d52866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22026, d52866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22027 q = 1) (hb : d52867 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22027, d52867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22027, d52867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d123111 q = 1) (hb : d170178 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123111, d170178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d123111, d170178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d22033 q = 1) (hb : d123112 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22033, d123112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22033, d123112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48870 q ha hb
  have h9 (q : Pattern) (ha : d21841 q = 1) (hb : d101284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21841, d101284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48870 q ha hb
    | true =>
      simp only [d21841, d101284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d22034 q = 1) (hb : d123113 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22034, d123113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22034, d123113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21842 q = 1) (hb : d101286 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21842, d101286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21842, d101286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d22035 q = 1) (hb : d123114 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22035, d123114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22035, d123114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22036 q = 1) (hb : d123115 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22036, d123115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22036, d123115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d123116 q = 1) (hb : d170179 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123116, d170179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d123116, d170179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d123117 q = 1) (hb : d170180 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123117, d170180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123117, d170180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49565 (p : Pattern) (ha : d123124 p = 1) (hb : d170183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22028 q = 1) (hb : d52868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22028, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22028, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46151 q ha hb
  have h2 (q : Pattern) (ha : d21737 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21737, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46151 q ha hb
    | true =>
      simp only [d21737, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22029 q = 1) (hb : d52869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22029, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22029, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21738 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21738, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21738, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22030 q = 1) (hb : d52870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22030, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22030, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22031 q = 1) (hb : d52871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22031, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22031, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d123118 q = 1) (hb : d170181 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123118, d170181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d123118, d170181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d22037 q = 1) (hb : d123119 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22037, d123119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22037, d123119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48843 q ha hb
  have h9 (q : Pattern) (ha : d21748 q = 1) (hb : d101299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21748, d101299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48843 q ha hb
    | true =>
      simp only [d21748, d101299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d22038 q = 1) (hb : d123120 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22038, d123120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22038, d123120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21749 q = 1) (hb : d101301 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21749, d101301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21749, d101301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d22039 q = 1) (hb : d123121 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22039, d123121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22039, d123121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22040 q = 1) (hb : d123122 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22040, d123122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22040, d123122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d123123 q = 1) (hb : d170182 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123123, d170182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d123123, d170182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d123124 q = 1) (hb : d170183 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123124, d170183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123124, d170183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49566 (p : Pattern) (ha : d123134 p = 1) (hb : d170188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22053 q = 1) (hb : d113452 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22053, d113452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22053, d113452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46167 q ha hb
  have h2 (q : Pattern) (ha : d21851 q = 1) (hb : d101335 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21851, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46167 q ha hb
    | true =>
      simp only [d21851, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22054 q = 1) (hb : d113453 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22054, d113453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22054, d113453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21852 q = 1) (hb : d101337 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21852, d101337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21852, d101337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22055 q = 1) (hb : d113454 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22055, d113454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22055, d113454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22056 q = 1) (hb : d113455 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22056, d113455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22056, d113455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d123128 q = 1) (hb : d170187 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123128, d170187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d123128, d170187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d13164 q = 1) (hb : d123129 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13164, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13164, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33439 q ha hb
  have h9 (q : Pattern) (ha : d13025 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33439 q ha hb
    | true =>
      simp only [d13025, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13165 q = 1) (hb : d123130 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13165, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13165, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13026 q = 1) (hb : d101323 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13026, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13166 q = 1) (hb : d123131 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13166, d123131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13166, d123131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13167 q = 1) (hb : d123132 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13167, d123132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13167, d123132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d22058 q = 1) (hb : d123133 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22058, d123133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22058, d123133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d123134 q = 1) (hb : d170188 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123134, d170188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123134, d170188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro49567 (p : Pattern) (ha : d123140 p = 1) (hb : d170194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22043 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22043, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22043, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46147 q ha hb
  have h2 (q : Pattern) (ha : d21742 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46147 q ha hb
    | true =>
      simp only [d21742, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22044 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22044, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22044, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21743 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21743, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22045 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22045, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22045, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22046 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22046, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22046, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d123139 q = 1) (hb : d170193 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123139, d170193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d123139, d170193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d13164 q = 1) (hb : d123129 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13164, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13164, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33439 q ha hb
  have h9 (q : Pattern) (ha : d13025 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33439 q ha hb
    | true =>
      simp only [d13025, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13165 q = 1) (hb : d123130 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13165, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13165, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13026 q = 1) (hb : d101323 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13026, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13166 q = 1) (hb : d123131 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13166, d123131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13166, d123131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13167 q = 1) (hb : d123132 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13167, d123132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13167, d123132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d22058 q = 1) (hb : d123133 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22058, d123133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22058, d123133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d123140 q = 1) (hb : d170194 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123140, d170194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123140, d170194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro49568 (p : Pattern) (ha : d123155 p = 1) (hb : d170203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123125 q = 1) (hb : d170184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123125, d170184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49564 q ha hb
    | true =>
      simp only [d123125, d170184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49565 q ha hb
  have h2 (q : Pattern) (ha : d123126 q = 1) (hb : d170185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123126, d170185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123126, d170185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123127 q = 1) (hb : d170186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123127, d170186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123127, d170186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123135 q = 1) (hb : d170189 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123135, d170189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49565 q ha hb
    | true =>
      simp only [d123135, d170189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49566 q ha hb
  have h5 (q : Pattern) (ha : d123136 q = 1) (hb : d170190 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123136, d170190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123136, d170190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123137 q = 1) (hb : d170191 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123137, d170191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123137, d170191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123138 q = 1) (hb : d170192 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123138, d170192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123138, d170192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123141 q = 1) (hb : d170195 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123141, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49565 q ha hb
    | true =>
      simp only [d123141, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49567 q ha hb
  have h9 (q : Pattern) (ha : d123142 q = 1) (hb : d170196 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123142, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123142, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123143 q = 1) (hb : d170197 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123143, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123143, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123150 q = 1) (hb : d170198 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123150, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49567 q ha hb
    | true =>
      simp only [d123150, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48890 q hb ha
  have h12 (q : Pattern) (ha : d123151 q = 1) (hb : d170199 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123151, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123151, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123152 q = 1) (hb : d170200 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123152, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123152, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123153 q = 1) (hb : d170201 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123153, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123153, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123154 q = 1) (hb : d170202 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123154, d170202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123154, d170202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123155 q = 1) (hb : d170203 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123155, d170203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123155, d170203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro49569 (p : Pattern) (ha : d123160 p = 1) (hb : d170208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123141 q = 1) (hb : d170195 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123141, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49565 q ha hb
    | true =>
      simp only [d123141, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49567 q ha hb
  have h2 (q : Pattern) (ha : d123142 q = 1) (hb : d170196 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123142, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123142, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123143 q = 1) (hb : d170197 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123143, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123143, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123150 q = 1) (hb : d170198 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123150, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49567 q ha hb
    | true =>
      simp only [d123150, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48890 q hb ha
  have h5 (q : Pattern) (ha : d123151 q = 1) (hb : d170199 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123151, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123151, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123152 q = 1) (hb : d170200 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123152, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123152, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123153 q = 1) (hb : d170201 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123153, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123153, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123158 q = 1) (hb : d170206 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123158, d170206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123158, d170206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123159 q = 1) (hb : d170207 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123159, d170207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123159, d170207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123160 q = 1) (hb : d170208 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123160, d170208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d123160, d170208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro49570 (p : Pattern) (ha : d123166 p = 1) (hb : d170214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123156 q = 1) (hb : d170204 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123156, d170204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49568 q ha hb
    | true =>
      simp only [d123156, d170204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123157 q = 1) (hb : d170205 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123157, d170205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123157, d170205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123161 q = 1) (hb : d170209 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123161, d170209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49569 q ha hb
    | true =>
      simp only [d123161, d170209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123162 q = 1) (hb : d170210 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123162, d170210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123162, d170210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123163 q = 1) (hb : d170211 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123163, d170211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123163, d170211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123164 q = 1) (hb : d170212 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123164, d170212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123164, d170212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123165 q = 1) (hb : d170213 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123165, d170213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123165, d170213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123166 q = 1) (hb : d170214 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123166, d170214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123166, d170214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49571 (p : Pattern) (ha : d123173 p = 1) (hb : d170220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123168 q = 1) (hb : d170215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123168, d170215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49567 q ha hb
    | true =>
      simp only [d123168, d170215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48862 q hb ha
  have h2 (q : Pattern) (ha : d123169 q = 1) (hb : d170216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123169, d170216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123169, d170216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123170 q = 1) (hb : d170217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123170, d170217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123170, d170217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123171 q = 1) (hb : d170218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123171, d170218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123171, d170218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123172 q = 1) (hb : d170219 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123172, d170219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123172, d170219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123173 q = 1) (hb : d170220 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123173, d170220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123173, d170220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49572 (p : Pattern) (ha : d123179 p = 1) (hb : d170226 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123161 q = 1) (hb : d170209 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123161, d170209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49569 q ha hb
    | true =>
      simp only [d123161, d170209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123162 q = 1) (hb : d170210 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123162, d170210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123162, d170210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123174 q = 1) (hb : d170221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123174, d170221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49571 q ha hb
    | true =>
      simp only [d123174, d170221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123175 q = 1) (hb : d170222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123175, d170222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123175, d170222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123176 q = 1) (hb : d170223 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123176, d170223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123176, d170223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123177 q = 1) (hb : d170224 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123177, d170224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123177, d170224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123178 q = 1) (hb : d170225 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123178, d170225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123178, d170225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123179 q = 1) (hb : d170226 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123179, d170226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123179, d170226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49573 (p : Pattern) (ha : d123200 p = 1) (hb : d170234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123141 q = 1) (hb : d170195 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123141, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49565 q ha hb
    | true =>
      simp only [d123141, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49567 q ha hb
  have h2 (q : Pattern) (ha : d123142 q = 1) (hb : d170196 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123142, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123142, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123143 q = 1) (hb : d170197 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123143, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123143, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123150 q = 1) (hb : d170198 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123150, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49567 q ha hb
    | true =>
      simp only [d123150, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48890 q hb ha
  have h5 (q : Pattern) (ha : d123151 q = 1) (hb : d170199 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123151, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123151, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123152 q = 1) (hb : d170200 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123152, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123152, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123153 q = 1) (hb : d170201 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123153, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123153, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123195 q = 1) (hb : d170229 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123195, d170229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49567 q ha hb
    | true =>
      simp only [d123195, d170229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46195 q hb ha
  have h9 (q : Pattern) (ha : d123196 q = 1) (hb : d170230 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123196, d170230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123196, d170230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123197 q = 1) (hb : d170231 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123197, d170231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123197, d170231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123198 q = 1) (hb : d170232 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123198, d170232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123198, d170232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123199 q = 1) (hb : d170233 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123199, d170233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123199, d170233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123200 q = 1) (hb : d170234 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123200, d170234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123200, d170234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro49574 (p : Pattern) (ha : d123206 p = 1) (hb : d170240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123201 q = 1) (hb : d170235 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123201, d170235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49573 q ha hb
    | true =>
      simp only [d123201, d170235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123202 q = 1) (hb : d170236 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123202, d170236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123202, d170236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123203 q = 1) (hb : d170237 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123203, d170237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123203, d170237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123204 q = 1) (hb : d170238 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123204, d170238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123204, d170238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123205 q = 1) (hb : d170239 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123205, d170239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123205, d170239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123206 q = 1) (hb : d170240 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123206, d170240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123206, d170240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49575 (p : Pattern) (ha : d123212 p = 1) (hb : d170246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123180 q = 1) (hb : d170227 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123180, d170227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49570 q ha hb
    | true =>
      simp only [d123180, d170227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49572 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123193 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123194 q = 1) (hb : d170228 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123194, d170228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123194, d170228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d123207 q = 1) (hb : d170241 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123207, d170241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49574 q ha hb
    | true =>
      simp only [d123207, d170241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123208 q = 1) (hb : d170242 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123208, d170242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123208, d170242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123209 q = 1) (hb : d170243 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123209, d170243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123209, d170243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123210 q = 1) (hb : d170244 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123210, d170244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123210, d170244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123211 q = 1) (hb : d170245 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123211, d170245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123211, d170245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123212 q = 1) (hb : d170246 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123212, d170246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123212, d170246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro49576 (p : Pattern) (ha : d123192 p = 1) (hb : d170251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123174 q = 1) (hb : d170221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123174, d170221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49571 q ha hb
    | true =>
      simp only [d123174, d170221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123175 q = 1) (hb : d170222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123175, d170222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123175, d170222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123189 q = 1) (hb : d170248 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123189, d170248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123189, d170248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123190 q = 1) (hb : d170249 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123190, d170249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123190, d170249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123191 q = 1) (hb : d170250 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123191, d170250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123191, d170250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123192 q = 1) (hb : d170251 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123192, d170251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123192, d170251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49577 (p : Pattern) (ha : d123219 p = 1) (hb : d170257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123214 q = 1) (hb : d170252 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123214, d170252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49576 q ha hb
    | true =>
      simp only [d123214, d170252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123215 q = 1) (hb : d170253 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123215, d170253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123215, d170253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123216 q = 1) (hb : d170254 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123216, d170254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123216, d170254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123217 q = 1) (hb : d170255 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123217, d170255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123217, d170255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123218 q = 1) (hb : d170256 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123218, d170256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123218, d170256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123219 q = 1) (hb : d170257 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123219, d170257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123219, d170257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49578 (p : Pattern) (ha : d123225 p = 1) (hb : d170263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122976 q = 1) (hb : d170045 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122976, d170045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122976, d170045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49535 q ha hb
  have h2 (q : Pattern) (ha : d122977 q = 1) (hb : d170046 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122977, d170046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122977, d170046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122986 q = 1) (hb : d170055 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122986, d170055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49535 q ha hb
    | true =>
      simp only [d122986, d170055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49538 q ha hb
  have h4 (q : Pattern) (ha : d122987 q = 1) (hb : d170056 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122987, d170056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122987, d170056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122988 q = 1) (hb : d170057 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122988, d170057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122988, d170057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123079 q = 1) (hb : d170146 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123079, d170146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49551 q ha hb
    | true =>
      simp only [d123079, d170146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49559 q ha hb
  have h7 (q : Pattern) (ha : d123097 q = 1) (hb : d170164 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123097, d170164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49560 q ha hb
    | true =>
      simp only [d123097, d170164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49561 q ha hb
  have h8 (q : Pattern) (ha : d123098 q = 1) (hb : d170165 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123098, d170165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123098, d170165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123099 q = 1) (hb : d170166 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123099, d170166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123099, d170166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123100 q = 1) (hb : d170167 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123100, d170167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123100, d170167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123104 q = 1) (hb : d170171 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123104, d170171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123104, d170171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49562 q ha hb
  have h12 (q : Pattern) (ha : d123106 q = 1) (hb : d170173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123106, d170173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123106, d170173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49563 q ha hb
  have h13 (q : Pattern) (ha : d123107 q = 1) (hb : d170174 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123107, d170174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123107, d170174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123108 q = 1) (hb : d170175 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123108, d170175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123108, d170175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d123109 q = 1) (hb : d170176 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123109, d170176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d123109, d170176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d123110 q = 1) (hb : d170177 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123110, d170177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123110, d170177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d123213 q = 1) (hb : d170247 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123213, d170247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123213, d170247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49575 q ha hb
  have h18 (q : Pattern) (ha : d123220 q = 1) (hb : d170258 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123220, d170258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123220, d170258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49577 q ha hb
  have h19 (q : Pattern) (ha : d123221 q = 1) (hb : d170259 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123221, d170259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123221, d170259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d123222 q = 1) (hb : d170260 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123222, d170260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d123222, d170260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d123223 q = 1) (hb : d170261 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123223, d170261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d123223, d170261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d123224 q = 1) (hb : d170262 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123224, d170262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d123224, d170262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d123225 q = 1) (hb : d170263 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d123225, d170263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d123225, d170263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro49579 (p : Pattern) (ha : d123231 p = 1) (hb : d170269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123226 q = 1) (hb : d170264 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d123226, d170264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123226, d170264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49578 q ha hb
  have h2 (q : Pattern) (ha : d123227 q = 1) (hb : d170265 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d123227, d170265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123227, d170265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123228 q = 1) (hb : d170266 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d123228, d170266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123228, d170266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123229 q = 1) (hb : d170267 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d123229, d170267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123229, d170267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123230 q = 1) (hb : d170268 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d123230, d170268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123230, d170268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123231 q = 1) (hb : d170269 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d123231, d170269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123231, d170269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49580 (p : Pattern) (ha : d123239 p = 1) (hb : d170275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10036 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46211 q ha hb
    | true =>
      simp only [d10036, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10038 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10038, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16859 q = 1) (hb : d52998 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16859, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16859, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16860 q = 1) (hb : d52999 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16860, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16860, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d123235 q = 1) (hb : d170273 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123235, d170273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123235, d170273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d22226 q = 1) (hb : d101490 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22226, d101490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48900 q ha hb
    | true =>
      simp only [d22226, d101490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22227 q = 1) (hb : d101492 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22227, d101492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22227, d101492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22228 q = 1) (hb : d123236 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22228, d123236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22228, d123236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22229 q = 1) (hb : d123237 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22229, d123237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22229, d123237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d123238 q = 1) (hb : d170274 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123238, d170274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d123238, d170274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d123239 q = 1) (hb : d170275 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123239, d170275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123239, d170275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49581 (p : Pattern) (ha : d123244 p = 1) (hb : d170277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22220 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46207 q ha hb
    | true =>
      simp only [d22220, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22221 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22221, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22222 q = 1) (hb : d53013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22222, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22222, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22223 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22223, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22223, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d123240 q = 1) (hb : d170276 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123240, d170276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123240, d170276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d13351 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33494 q ha hb
    | true =>
      simp only [d13351, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13352 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13352, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13353 q = 1) (hb : d123241 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13353, d123241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13353, d123241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13354 q = 1) (hb : d123242 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13354, d123242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13354, d123242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d22238 q = 1) (hb : d123243 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22238, d123243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22238, d123243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d123244 q = 1) (hb : d170277 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123244, d170277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123244, d170277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro49582 (p : Pattern) (ha : d123262 p = 1) (hb : d170290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123245 q = 1) (hb : d170278 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123245, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49580 q ha hb
    | true =>
      simp only [d123245, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49581 q ha hb
  have h2 (q : Pattern) (ha : d123246 q = 1) (hb : d170279 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123246, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123246, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123247 q = 1) (hb : d170280 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123247, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123247, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123252 q = 1) (hb : d170281 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123252, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49581 q ha hb
    | true =>
      simp only [d123252, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48903 q hb ha
  have h5 (q : Pattern) (ha : d123253 q = 1) (hb : d170282 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123253, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123253, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123254 q = 1) (hb : d170283 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123254, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123254, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123255 q = 1) (hb : d170284 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123255, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123255, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123257 q = 1) (hb : d170285 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123257, d170285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49581 q ha hb
    | true =>
      simp only [d123257, d170285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48904 q hb ha
  have h9 (q : Pattern) (ha : d123258 q = 1) (hb : d170286 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123258, d170286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123258, d170286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123259 q = 1) (hb : d170287 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123259, d170287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123259, d170287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123260 q = 1) (hb : d170288 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123260, d170288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123260, d170288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123261 q = 1) (hb : d170289 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123261, d170289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123261, d170289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123262 q = 1) (hb : d170290 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123262, d170290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123262, d170290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro49583 (p : Pattern) (ha : d123266 p = 1) (hb : d170294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123257 q = 1) (hb : d170285 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123257, d170285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49581 q ha hb
    | true =>
      simp only [d123257, d170285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48904 q hb ha
  have h2 (q : Pattern) (ha : d123258 q = 1) (hb : d170286 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123258, d170286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123258, d170286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123259 q = 1) (hb : d170287 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123259, d170287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123259, d170287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123260 q = 1) (hb : d170288 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123260, d170288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123260, d170288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123265 q = 1) (hb : d170293 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123265, d170293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123265, d170293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123266 q = 1) (hb : d170294 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123266, d170294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123266, d170294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49584 (p : Pattern) (ha : d123272 p = 1) (hb : d170300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123263 q = 1) (hb : d170291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123263, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49582 q ha hb
    | true =>
      simp only [d123263, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123264 q = 1) (hb : d170292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123264, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123264, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123267 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49583 q ha hb
    | true =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123268 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123269 q = 1) (hb : d170297 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123269, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123269, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123270 q = 1) (hb : d170298 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123270, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123270, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123271 q = 1) (hb : d170299 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123271, d170299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123271, d170299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123272 q = 1) (hb : d170300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123272, d170300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123272, d170300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49585 (p : Pattern) (ha : d123276 p = 1) (hb : d170304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123267 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49583 q ha hb
    | true =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123268 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123273 q = 1) (hb : d170301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123273, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123273, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123274 q = 1) (hb : d170302 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123274, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123274, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123275 q = 1) (hb : d170303 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123275, d170303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123275, d170303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123276 q = 1) (hb : d170304 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123276, d170304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123276, d170304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49586 (p : Pattern) (ha : d123282 p = 1) (hb : d170310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123277 q = 1) (hb : d170305 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123277, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49584 q ha hb
    | true =>
      simp only [d123277, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49585 q ha hb
  have h2 (q : Pattern) (ha : d123278 q = 1) (hb : d170306 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123278, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123278, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123279 q = 1) (hb : d170307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123279, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123279, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123280 q = 1) (hb : d170308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123280, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123280, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123281 q = 1) (hb : d170309 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123281, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123281, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123282 q = 1) (hb : d170310 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123282, d170310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123282, d170310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49587 (p : Pattern) (ha : d123285 p = 1) (hb : d170313 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123263 q = 1) (hb : d170291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123263, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49582 q ha hb
    | true =>
      simp only [d123263, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123264 q = 1) (hb : d170292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123264, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123264, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123267 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49583 q ha hb
    | true =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123268 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123269 q = 1) (hb : d170297 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123269, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123269, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123270 q = 1) (hb : d170298 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123270, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123270, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123271 q = 1) (hb : d170299 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123271, d170299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123271, d170299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123285 q = 1) (hb : d170313 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123285, d170313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123285, d170313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49588 (p : Pattern) (ha : d123286 p = 1) (hb : d170314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123267 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49583 q ha hb
    | true =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123268 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123273 q = 1) (hb : d170301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123273, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123273, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123274 q = 1) (hb : d170302 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123274, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123274, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123275 q = 1) (hb : d170303 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123275, d170303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123275, d170303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123286 q = 1) (hb : d170314 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123286, d170314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123286, d170314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49589 (p : Pattern) (ha : d123292 p = 1) (hb : d170320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123277 q = 1) (hb : d170305 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123277, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49584 q ha hb
    | true =>
      simp only [d123277, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49585 q ha hb
  have h2 (q : Pattern) (ha : d123278 q = 1) (hb : d170306 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123278, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123278, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123279 q = 1) (hb : d170307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123279, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123279, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123280 q = 1) (hb : d170308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123280, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123280, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123281 q = 1) (hb : d170309 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123281, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123281, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123287 q = 1) (hb : d170315 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123287, d170315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49587 q ha hb
    | true =>
      simp only [d123287, d170315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49588 q ha hb
  have h7 (q : Pattern) (ha : d123288 q = 1) (hb : d170316 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123288, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123288, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123289 q = 1) (hb : d170317 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123289, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123289, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123290 q = 1) (hb : d170318 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123290, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123290, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123291 q = 1) (hb : d170319 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123291, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123291, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123292 q = 1) (hb : d170320 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123292, d170320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123292, d170320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49590 (p : Pattern) (ha : d123297 p = 1) (hb : d170325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123263 q = 1) (hb : d170291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123263, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49582 q ha hb
    | true =>
      simp only [d123263, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123264 q = 1) (hb : d170292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123264, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123264, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123267 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49583 q ha hb
    | true =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123268 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123269 q = 1) (hb : d170297 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123269, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123269, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123270 q = 1) (hb : d170298 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123270, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123270, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123296 q = 1) (hb : d170324 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123296, d170324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123296, d170324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123297 q = 1) (hb : d170325 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123297, d170325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123297, d170325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49591 (p : Pattern) (ha : d123299 p = 1) (hb : d170327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123267 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49583 q ha hb
    | true =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123268 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123273 q = 1) (hb : d170301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123273, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123273, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123274 q = 1) (hb : d170302 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123274, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123274, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123298 q = 1) (hb : d170326 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123298, d170326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123298, d170326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123299 q = 1) (hb : d170327 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123299, d170327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123299, d170327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49592 (p : Pattern) (ha : d123306 p = 1) (hb : d170334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123263 q = 1) (hb : d170291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123263, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49582 q ha hb
    | true =>
      simp only [d123263, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123264 q = 1) (hb : d170292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123264, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123264, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123267 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49583 q ha hb
    | true =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123268 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123269 q = 1) (hb : d170297 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123269, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123269, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123304 q = 1) (hb : d170332 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123304, d170332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123304, d170332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123305 q = 1) (hb : d170333 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123305, d170333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123305, d170333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123306 q = 1) (hb : d170334 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123306, d170334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123306, d170334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49593 (p : Pattern) (ha : d123309 p = 1) (hb : d170337 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123267 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49583 q ha hb
    | true =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123268 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123273 q = 1) (hb : d170301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123273, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123273, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123307 q = 1) (hb : d170335 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123307, d170335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123307, d170335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123308 q = 1) (hb : d170336 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123308, d170336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123308, d170336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123309 q = 1) (hb : d170337 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123309, d170337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123309, d170337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49594 (p : Pattern) (ha : d123317 p = 1) (hb : d170342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22313 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22313, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46225 q ha hb
    | true =>
      simp only [d22313, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22314 q = 1) (hb : d53107 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22314, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22314, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22315 q = 1) (hb : d53108 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22315, d53108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22315, d53108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22316 q = 1) (hb : d53109 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22316, d53109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22316, d53109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d123313 q = 1) (hb : d170341 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123313, d170341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123313, d170341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d10046 q = 1) (hb : d101473 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23339 q ha hb
    | true =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10048 q = 1) (hb : d101475 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15229 q = 1) (hb : d123314 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15229, d123314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15229, d123314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15230 q = 1) (hb : d123315 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15230, d123315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15230, d123315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15231 q = 1) (hb : d123316 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15231, d123316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15231, d123316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d123317 q = 1) (hb : d170342 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123317, d170342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123317, d170342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro49595 (p : Pattern) (ha : d123322 p = 1) (hb : d170347 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22324 q = 1) (hb : d101526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22324, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46227 q ha hb
    | true =>
      simp only [d22324, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22325 q = 1) (hb : d101528 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22325, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22325, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22326 q = 1) (hb : d113608 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22326, d113608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22326, d113608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22327 q = 1) (hb : d113609 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22327, d113609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22327, d113609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d123321 q = 1) (hb : d170346 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123321, d170346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123321, d170346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d13351 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33494 q ha hb
    | true =>
      simp only [d13351, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13352 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13352, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13353 q = 1) (hb : d123241 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13353, d123241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13353, d123241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13354 q = 1) (hb : d123242 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13354, d123242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13354, d123242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d22238 q = 1) (hb : d123243 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22238, d123243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22238, d123243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d123322 q = 1) (hb : d170347 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123322, d170347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123322, d170347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro49596 (p : Pattern) (ha : d123328 p = 1) (hb : d170353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123318 q = 1) (hb : d170343 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123318, d170343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49594 q ha hb
    | true =>
      simp only [d123318, d170343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49580 q ha hb
  have h2 (q : Pattern) (ha : d123319 q = 1) (hb : d170344 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123319, d170344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123319, d170344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123320 q = 1) (hb : d170345 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123320, d170345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123320, d170345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123323 q = 1) (hb : d170348 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123323, d170348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49580 q ha hb
    | true =>
      simp only [d123323, d170348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49595 q ha hb
  have h5 (q : Pattern) (ha : d123324 q = 1) (hb : d170349 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123324, d170349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123324, d170349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123325 q = 1) (hb : d170350 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123325, d170350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123325, d170350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123326 q = 1) (hb : d170351 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123326, d170351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123326, d170351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123245 q = 1) (hb : d170278 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123245, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49580 q ha hb
    | true =>
      simp only [d123245, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49581 q ha hb
  have h9 (q : Pattern) (ha : d123246 q = 1) (hb : d170279 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123246, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123246, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123247 q = 1) (hb : d170280 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123247, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123247, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123252 q = 1) (hb : d170281 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123252, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49581 q ha hb
    | true =>
      simp only [d123252, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48903 q hb ha
  have h12 (q : Pattern) (ha : d123253 q = 1) (hb : d170282 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123253, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123253, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123254 q = 1) (hb : d170283 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123254, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123254, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123255 q = 1) (hb : d170284 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123255, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123255, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123327 q = 1) (hb : d170352 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123327, d170352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123327, d170352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123328 q = 1) (hb : d170353 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123328, d170353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123328, d170353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro49597 (p : Pattern) (ha : d123333 p = 1) (hb : d170358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123245 q = 1) (hb : d170278 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123245, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49580 q ha hb
    | true =>
      simp only [d123245, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49581 q ha hb
  have h2 (q : Pattern) (ha : d123246 q = 1) (hb : d170279 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123246, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123246, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123247 q = 1) (hb : d170280 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123247, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123247, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123252 q = 1) (hb : d170281 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123252, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49581 q ha hb
    | true =>
      simp only [d123252, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48903 q hb ha
  have h5 (q : Pattern) (ha : d123253 q = 1) (hb : d170282 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123253, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123253, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123254 q = 1) (hb : d170283 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123254, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123254, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123255 q = 1) (hb : d170284 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123255, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123255, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123331 q = 1) (hb : d170356 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123331, d170356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123331, d170356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123332 q = 1) (hb : d170357 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123332, d170357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123332, d170357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123333 q = 1) (hb : d170358 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123333, d170358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d123333, d170358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro49598 (p : Pattern) (ha : d123339 p = 1) (hb : d170364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123329 q = 1) (hb : d170354 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123329, d170354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49596 q ha hb
    | true =>
      simp only [d123329, d170354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123330 q = 1) (hb : d170355 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123330, d170355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123330, d170355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123334 q = 1) (hb : d170359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123334, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49597 q ha hb
    | true =>
      simp only [d123334, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123335 q = 1) (hb : d170360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123335, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123335, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123336 q = 1) (hb : d170361 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123336, d170361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123336, d170361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123337 q = 1) (hb : d170362 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123337, d170362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123337, d170362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123338 q = 1) (hb : d170363 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123338, d170363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123338, d170363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123339 q = 1) (hb : d170364 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123339, d170364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123339, d170364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49599 (p : Pattern) (ha : d123343 p = 1) (hb : d170368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123334 q = 1) (hb : d170359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123334, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49597 q ha hb
    | true =>
      simp only [d123334, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123335 q = 1) (hb : d170360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123335, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123335, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123267 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49583 q ha hb
    | true =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123268 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123340 q = 1) (hb : d170365 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123340, d170365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123340, d170365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123341 q = 1) (hb : d170366 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123341, d170366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123341, d170366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123342 q = 1) (hb : d170367 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123342, d170367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123342, d170367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123343 q = 1) (hb : d170368 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123343, d170368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123343, d170368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49600 (p : Pattern) (ha : d123351 p = 1) (hb : d170376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123245 q = 1) (hb : d170278 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123245, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49580 q ha hb
    | true =>
      simp only [d123245, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49581 q ha hb
  have h2 (q : Pattern) (ha : d123246 q = 1) (hb : d170279 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123246, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123246, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123247 q = 1) (hb : d170280 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123247, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123247, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123252 q = 1) (hb : d170281 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123252, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49581 q ha hb
    | true =>
      simp only [d123252, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48903 q hb ha
  have h5 (q : Pattern) (ha : d123253 q = 1) (hb : d170282 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123253, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123253, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123254 q = 1) (hb : d170283 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123254, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123254, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123255 q = 1) (hb : d170284 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123255, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123255, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123346 q = 1) (hb : d170371 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123346, d170371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49581 q ha hb
    | true =>
      simp only [d123346, d170371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46206 q hb ha
  have h9 (q : Pattern) (ha : d123347 q = 1) (hb : d170372 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123347, d170372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123347, d170372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123348 q = 1) (hb : d170373 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123348, d170373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123348, d170373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123349 q = 1) (hb : d170374 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123349, d170374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123349, d170374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123350 q = 1) (hb : d170375 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123350, d170375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123350, d170375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123351 q = 1) (hb : d170376 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123351, d170376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123351, d170376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro49601 (p : Pattern) (ha : d123357 p = 1) (hb : d170382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123352 q = 1) (hb : d170377 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123352, d170377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49600 q ha hb
    | true =>
      simp only [d123352, d170377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123353 q = 1) (hb : d170378 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123353, d170378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123353, d170378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123354 q = 1) (hb : d170379 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123354, d170379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123354, d170379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123355 q = 1) (hb : d170380 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123355, d170380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123355, d170380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123356 q = 1) (hb : d170381 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123356, d170381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123356, d170381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123357 q = 1) (hb : d170382 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123357, d170382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123357, d170382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49602 (p : Pattern) (ha : d123363 p = 1) (hb : d170388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123300 q = 1) (hb : d170328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123300, d170328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49590 q ha hb
    | true =>
      simp only [d123300, d170328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49591 q ha hb
  have h2 (q : Pattern) (ha : d123301 q = 1) (hb : d170329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123301, d170329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123301, d170329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123302 q = 1) (hb : d170330 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123302, d170330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123302, d170330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123303 q = 1) (hb : d170331 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123303, d170331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123303, d170331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123310 q = 1) (hb : d170338 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123310, d170338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49592 q ha hb
    | true =>
      simp only [d123310, d170338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49593 q ha hb
  have h6 (q : Pattern) (ha : d123311 q = 1) (hb : d170339 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123311, d170339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123311, d170339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123312 q = 1) (hb : d170340 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123312, d170340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123312, d170340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123344 q = 1) (hb : d170369 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123344, d170369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49598 q ha hb
    | true =>
      simp only [d123344, d170369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49599 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123277 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d123345 q = 1) (hb : d170370 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123345, d170370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123345, d170370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d123358 q = 1) (hb : d170383 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123358, d170383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49601 q ha hb
    | true =>
      simp only [d123358, d170383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123359 q = 1) (hb : d170384 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123359, d170384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123359, d170384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d123360 q = 1) (hb : d170385 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123360, d170385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123360, d170385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123361 q = 1) (hb : d170386 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123361, d170386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123361, d170386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123362 q = 1) (hb : d170387 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123362, d170387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123362, d170387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123363 q = 1) (hb : d170388 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123363, d170388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123363, d170388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro49603 (p : Pattern) (ha : d123364 p = 1) (hb : d170389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123263 q = 1) (hb : d170291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123263, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49582 q ha hb
    | true =>
      simp only [d123263, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123264 q = 1) (hb : d170292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123264, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123264, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123267 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49583 q ha hb
    | true =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123268 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123269 q = 1) (hb : d170297 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123269, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123269, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123270 q = 1) (hb : d170298 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123270, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123270, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123296 q = 1) (hb : d170324 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123296, d170324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123296, d170324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123364 q = 1) (hb : d170389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123364, d170389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123364, d170389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49604 (p : Pattern) (ha : d123365 p = 1) (hb : d170390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123267 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49583 q ha hb
    | true =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123268 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123273 q = 1) (hb : d170301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123273, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123273, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123274 q = 1) (hb : d170302 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123274, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123274, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123298 q = 1) (hb : d170326 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123298, d170326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123298, d170326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123365 q = 1) (hb : d170390 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123365, d170390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123365, d170390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49605 (p : Pattern) (ha : d123370 p = 1) (hb : d170395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123263 q = 1) (hb : d170291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123263, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49582 q ha hb
    | true =>
      simp only [d123263, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123264 q = 1) (hb : d170292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123264, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123264, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123267 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49583 q ha hb
    | true =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123268 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123269 q = 1) (hb : d170297 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123269, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123269, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123304 q = 1) (hb : d170332 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123304, d170332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123304, d170332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123305 q = 1) (hb : d170333 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123305, d170333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123305, d170333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123370 q = 1) (hb : d170395 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123370, d170395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123370, d170395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49606 (p : Pattern) (ha : d123371 p = 1) (hb : d170396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123267 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49583 q ha hb
    | true =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123268 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123273 q = 1) (hb : d170301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123273, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123273, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123307 q = 1) (hb : d170335 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123307, d170335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123307, d170335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123308 q = 1) (hb : d170336 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123308, d170336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123308, d170336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123371 q = 1) (hb : d170396 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123371, d170396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123371, d170396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49607 (p : Pattern) (ha : d123375 p = 1) (hb : d170400 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123329 q = 1) (hb : d170354 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123329, d170354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49596 q ha hb
    | true =>
      simp only [d123329, d170354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123330 q = 1) (hb : d170355 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123330, d170355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123330, d170355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123334 q = 1) (hb : d170359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123334, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49597 q ha hb
    | true =>
      simp only [d123334, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123335 q = 1) (hb : d170360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123335, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123335, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123336 q = 1) (hb : d170361 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123336, d170361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123336, d170361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123337 q = 1) (hb : d170362 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123337, d170362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123337, d170362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123338 q = 1) (hb : d170363 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123338, d170363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123338, d170363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123375 q = 1) (hb : d170400 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123375, d170400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123375, d170400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49608 (p : Pattern) (ha : d123376 p = 1) (hb : d170401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123334 q = 1) (hb : d170359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123334, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49597 q ha hb
    | true =>
      simp only [d123334, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123335 q = 1) (hb : d170360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123335, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123335, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123267 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49583 q ha hb
    | true =>
      simp only [d123267, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123268 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123268, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123340 q = 1) (hb : d170365 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123340, d170365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123340, d170365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123341 q = 1) (hb : d170366 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123341, d170366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123341, d170366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123342 q = 1) (hb : d170367 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123342, d170367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123342, d170367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123376 q = 1) (hb : d170401 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123376, d170401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123376, d170401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49609 (p : Pattern) (ha : d123379 p = 1) (hb : d170404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123352 q = 1) (hb : d170377 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123352, d170377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49600 q ha hb
    | true =>
      simp only [d123352, d170377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123353 q = 1) (hb : d170378 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123353, d170378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123353, d170378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123354 q = 1) (hb : d170379 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123354, d170379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123354, d170379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123355 q = 1) (hb : d170380 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123355, d170380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123355, d170380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123356 q = 1) (hb : d170381 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123356, d170381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123356, d170381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123379 q = 1) (hb : d170404 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123379, d170404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123379, d170404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49610 (p : Pattern) (ha : d123385 p = 1) (hb : d170410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123300 q = 1) (hb : d170328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123300, d170328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49590 q ha hb
    | true =>
      simp only [d123300, d170328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49591 q ha hb
  have h2 (q : Pattern) (ha : d123301 q = 1) (hb : d170329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123301, d170329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123301, d170329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123302 q = 1) (hb : d170330 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123302, d170330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123302, d170330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123303 q = 1) (hb : d170331 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123303, d170331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123303, d170331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123310 q = 1) (hb : d170338 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123310, d170338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49592 q ha hb
    | true =>
      simp only [d123310, d170338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49593 q ha hb
  have h6 (q : Pattern) (ha : d123311 q = 1) (hb : d170339 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123311, d170339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123311, d170339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123312 q = 1) (hb : d170340 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123312, d170340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123312, d170340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123344 q = 1) (hb : d170369 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123344, d170369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49598 q ha hb
    | true =>
      simp only [d123344, d170369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49599 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123277 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d123345 q = 1) (hb : d170370 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123345, d170370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123345, d170370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d123358 q = 1) (hb : d170383 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123358, d170383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49601 q ha hb
    | true =>
      simp only [d123358, d170383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123359 q = 1) (hb : d170384 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123359, d170384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123359, d170384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d123360 q = 1) (hb : d170385 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123360, d170385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123360, d170385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123361 q = 1) (hb : d170386 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123361, d170386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123361, d170386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123362 q = 1) (hb : d170387 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123362, d170387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123362, d170387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123366 q = 1) (hb : d170391 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123366, d170391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49603 q ha hb
    | true =>
      simp only [d123366, d170391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49604 q ha hb
  have h17 (q : Pattern) (ha : d123367 q = 1) (hb : d170392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123367, d170392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123367, d170392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d123368 q = 1) (hb : d170393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123368, d170393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123368, d170393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d123369 q = 1) (hb : d170394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123369, d170394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123369, d170394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d123372 q = 1) (hb : d170397 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123372, d170397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49605 q ha hb
    | true =>
      simp only [d123372, d170397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49606 q ha hb
  have h21 (q : Pattern) (ha : d123373 q = 1) (hb : d170398 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123373, d170398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123373, d170398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d123374 q = 1) (hb : d170399 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123374, d170399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d123374, d170399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d123377 q = 1) (hb : d170402 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123377, d170402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49607 q ha hb
    | true =>
      simp only [d123377, d170402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49608 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d123287 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d123378 q = 1) (hb : d170403 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123378, d170403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d123378, d170403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d123380 q = 1) (hb : d170405 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123380, d170405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49609 q ha hb
    | true =>
      simp only [d123380, d170405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d123381 q = 1) (hb : d170406 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123381, d170406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d123381, d170406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d123382 q = 1) (hb : d170407 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123382, d170407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d123382, d170407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d123383 q = 1) (hb : d170408 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123383, d170408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d123383, d170408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d123384 q = 1) (hb : d170409 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123384, d170409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d123384, d170409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d123385 q = 1) (hb : d170410 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123385, d170410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123385, d170410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro49611 (p : Pattern) (ha : d123397 p = 1) (hb : d170422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123387 q = 1) (hb : d170412 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123387, d170412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49599 q ha hb
    | true =>
      simp only [d123387, d170412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49585 q ha hb
  have h2 (q : Pattern) (ha : d123388 q = 1) (hb : d170413 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123388, d170413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123388, d170413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123389 q = 1) (hb : d170414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123389, d170414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123389, d170414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123390 q = 1) (hb : d170415 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123390, d170415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123390, d170415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123391 q = 1) (hb : d170416 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123391, d170416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123391, d170416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123392 q = 1) (hb : d170417 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123392, d170417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49585 q ha hb
    | true =>
      simp only [d123392, d170417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123393 q = 1) (hb : d170418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123393, d170418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123393, d170418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123394 q = 1) (hb : d170419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123394, d170419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123394, d170419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123395 q = 1) (hb : d170420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123395, d170420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123395, d170420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123396 q = 1) (hb : d170421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123396, d170421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123396, d170421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123397 q = 1) (hb : d170422 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123397, d170422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123397, d170422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49612 (p : Pattern) (ha : d123403 p = 1) (hb : d170428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123392 q = 1) (hb : d170417 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123392, d170417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49585 q ha hb
    | true =>
      simp only [d123392, d170417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123393 q = 1) (hb : d170418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123393, d170418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123393, d170418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123394 q = 1) (hb : d170419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123394, d170419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123394, d170419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123395 q = 1) (hb : d170420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123395, d170420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123395, d170420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123396 q = 1) (hb : d170421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123396, d170421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123396, d170421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123398 q = 1) (hb : d170423 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123398, d170423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49588 q ha hb
    | true =>
      simp only [d123398, d170423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123399 q = 1) (hb : d170424 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123399, d170424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123399, d170424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123400 q = 1) (hb : d170425 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123400, d170425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123400, d170425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123401 q = 1) (hb : d170426 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123401, d170426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123401, d170426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123402 q = 1) (hb : d170427 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123402, d170427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123402, d170427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123403 q = 1) (hb : d170428 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123403, d170428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123403, d170428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49613 (p : Pattern) (ha : d123410 p = 1) (hb : d170435 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123377 q = 1) (hb : d170402 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123377, d170402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49607 q ha hb
    | true =>
      simp only [d123377, d170402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49608 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123287 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123378 q = 1) (hb : d170403 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123378, d170403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123378, d170403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d123380 q = 1) (hb : d170405 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123380, d170405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49609 q ha hb
    | true =>
      simp only [d123380, d170405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123381 q = 1) (hb : d170406 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123381, d170406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123381, d170406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123382 q = 1) (hb : d170407 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123382, d170407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123382, d170407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123408 q = 1) (hb : d170433 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123408, d170433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123408, d170433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123409 q = 1) (hb : d170434 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123409, d170434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123409, d170434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123410 q = 1) (hb : d170435 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123410, d170435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123410, d170435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro49614 (p : Pattern) (ha : d123412 p = 1) (hb : d170437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123398 q = 1) (hb : d170423 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123398, d170423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49588 q ha hb
    | true =>
      simp only [d123398, d170423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123399 q = 1) (hb : d170424 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123399, d170424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123399, d170424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123400 q = 1) (hb : d170425 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123400, d170425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123400, d170425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123401 q = 1) (hb : d170426 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123401, d170426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123401, d170426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123402 q = 1) (hb : d170427 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123402, d170427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123402, d170427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123412 q = 1) (hb : d170437 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123412, d170437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123412, d170437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49615 (p : Pattern) (ha : d123424 p = 1) (hb : d170444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22497 q = 1) (hb : d53179 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22497, d53179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22497, d53179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46225 q ha hb
  have h2 (q : Pattern) (ha : d22313 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22313, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46225 q ha hb
    | true =>
      simp only [d22313, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22498 q = 1) (hb : d53180 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22498, d53180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22498, d53180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22314 q = 1) (hb : d53107 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22314, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22314, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22499 q = 1) (hb : d53181 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22499, d53181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22499, d53181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22500 q = 1) (hb : d53182 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22500, d53182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22500, d53182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d123418 q = 1) (hb : d170443 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123418, d170443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d123418, d170443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d15380 q = 1) (hb : d123419 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15380, d123419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15380, d123419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23339 q ha hb
  have h9 (q : Pattern) (ha : d10046 q = 1) (hb : d101473 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23339 q ha hb
    | true =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15381 q = 1) (hb : d123420 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15381, d123420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15381, d123420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10048 q = 1) (hb : d101475 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15382 q = 1) (hb : d123421 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15382, d123421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15382, d123421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15383 q = 1) (hb : d123422 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15383, d123422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15383, d123422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15384 q = 1) (hb : d123423 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15384, d123423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15384, d123423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d123424 q = 1) (hb : d170444 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123424, d170444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123424, d170444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro49616 (p : Pattern) (ha : d123431 p = 1) (hb : d170447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17004 q = 1) (hb : d53183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17004, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46211 q ha hb
  have h2 (q : Pattern) (ha : d10036 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46211 q ha hb
    | true =>
      simp only [d10036, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17005 q = 1) (hb : d53184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17005, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10038 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10038, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17006 q = 1) (hb : d53185 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17006, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17006, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17007 q = 1) (hb : d53186 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17007, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17007, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d123425 q = 1) (hb : d170445 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123425, d170445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d123425, d170445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d22502 q = 1) (hb : d123426 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22502, d123426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22502, d123426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48900 q ha hb
  have h9 (q : Pattern) (ha : d22226 q = 1) (hb : d101490 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22226, d101490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48900 q ha hb
    | true =>
      simp only [d22226, d101490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d22503 q = 1) (hb : d123427 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22503, d123427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22503, d123427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22227 q = 1) (hb : d101492 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22227, d101492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22227, d101492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d22504 q = 1) (hb : d123428 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22504, d123428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22504, d123428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22505 q = 1) (hb : d123429 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22505, d123429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22505, d123429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d123430 q = 1) (hb : d170446 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123430, d170446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d123430, d170446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d123431 q = 1) (hb : d170447 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123431, d170447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123431, d170447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49617 (p : Pattern) (ha : d123441 p = 1) (hb : d170452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22518 q = 1) (hb : d113708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22518, d113708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22518, d113708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46227 q ha hb
  have h2 (q : Pattern) (ha : d22324 q = 1) (hb : d101526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22324, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46227 q ha hb
    | true =>
      simp only [d22324, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22519 q = 1) (hb : d113709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22519, d113709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22519, d113709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22325 q = 1) (hb : d101528 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22325, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22325, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22520 q = 1) (hb : d113710 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22520, d113710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22520, d113710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22521 q = 1) (hb : d113711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22521, d113711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22521, d113711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d123435 q = 1) (hb : d170451 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123435, d170451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d123435, d170451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d13490 q = 1) (hb : d123436 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13490, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13490, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33494 q ha hb
  have h9 (q : Pattern) (ha : d13351 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33494 q ha hb
    | true =>
      simp only [d13351, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13491 q = 1) (hb : d123437 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13491, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13491, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13352 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13352, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13492 q = 1) (hb : d123438 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13492, d123438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13492, d123438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13493 q = 1) (hb : d123439 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13493, d123439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13493, d123439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d22523 q = 1) (hb : d123440 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22523, d123440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22523, d123440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d123441 q = 1) (hb : d170452 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123441, d170452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123441, d170452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro49618 (p : Pattern) (ha : d123447 p = 1) (hb : d170458 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22508 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22508, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22508, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46207 q ha hb
  have h2 (q : Pattern) (ha : d22220 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46207 q ha hb
    | true =>
      simp only [d22220, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22509 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22509, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22509, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22221 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22221, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22510 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22510, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22510, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22511 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22511, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22511, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d123446 q = 1) (hb : d170457 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123446, d170457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d123446, d170457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d13490 q = 1) (hb : d123436 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13490, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13490, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33494 q ha hb
  have h9 (q : Pattern) (ha : d13351 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33494 q ha hb
    | true =>
      simp only [d13351, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13491 q = 1) (hb : d123437 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13491, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13491, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13352 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13352, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13492 q = 1) (hb : d123438 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13492, d123438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13492, d123438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13493 q = 1) (hb : d123439 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13493, d123439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13493, d123439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d22523 q = 1) (hb : d123440 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22523, d123440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22523, d123440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d123447 q = 1) (hb : d170458 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123447, d170458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123447, d170458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro49619 (p : Pattern) (ha : d123462 p = 1) (hb : d170467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123432 q = 1) (hb : d170448 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123432, d170448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49615 q ha hb
    | true =>
      simp only [d123432, d170448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49616 q ha hb
  have h2 (q : Pattern) (ha : d123433 q = 1) (hb : d170449 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123433, d170449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123433, d170449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123434 q = 1) (hb : d170450 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123434, d170450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123434, d170450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123442 q = 1) (hb : d170453 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123442, d170453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49616 q ha hb
    | true =>
      simp only [d123442, d170453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49617 q ha hb
  have h5 (q : Pattern) (ha : d123443 q = 1) (hb : d170454 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123443, d170454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123443, d170454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123444 q = 1) (hb : d170455 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123444, d170455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123444, d170455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123445 q = 1) (hb : d170456 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123445, d170456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123445, d170456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123448 q = 1) (hb : d170459 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123448, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49616 q ha hb
    | true =>
      simp only [d123448, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49618 q ha hb
  have h9 (q : Pattern) (ha : d123449 q = 1) (hb : d170460 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123449, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123449, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123450 q = 1) (hb : d170461 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123450, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123450, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123457 q = 1) (hb : d170462 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123457, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49618 q ha hb
    | true =>
      simp only [d123457, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48946 q hb ha
  have h12 (q : Pattern) (ha : d123458 q = 1) (hb : d170463 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123458, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123458, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123459 q = 1) (hb : d170464 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123459, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123459, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123460 q = 1) (hb : d170465 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123460, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123460, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123461 q = 1) (hb : d170466 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123461, d170466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123461, d170466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123462 q = 1) (hb : d170467 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123462, d170467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123462, d170467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro49620 (p : Pattern) (ha : d123467 p = 1) (hb : d170472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123448 q = 1) (hb : d170459 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123448, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49616 q ha hb
    | true =>
      simp only [d123448, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49618 q ha hb
  have h2 (q : Pattern) (ha : d123449 q = 1) (hb : d170460 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123449, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123449, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123450 q = 1) (hb : d170461 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123450, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123450, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123457 q = 1) (hb : d170462 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123457, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49618 q ha hb
    | true =>
      simp only [d123457, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48946 q hb ha
  have h5 (q : Pattern) (ha : d123458 q = 1) (hb : d170463 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123458, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123458, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123459 q = 1) (hb : d170464 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123459, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123459, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123460 q = 1) (hb : d170465 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123460, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123460, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123465 q = 1) (hb : d170470 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123465, d170470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123465, d170470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123466 q = 1) (hb : d170471 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123466, d170471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123466, d170471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123467 q = 1) (hb : d170472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123467, d170472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d123467, d170472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro49621 (p : Pattern) (ha : d123473 p = 1) (hb : d170478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123463 q = 1) (hb : d170468 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123463, d170468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49619 q ha hb
    | true =>
      simp only [d123463, d170468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123464 q = 1) (hb : d170469 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123464, d170469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123464, d170469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123468 q = 1) (hb : d170473 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123468, d170473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49620 q ha hb
    | true =>
      simp only [d123468, d170473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123469 q = 1) (hb : d170474 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123469, d170474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123469, d170474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123470 q = 1) (hb : d170475 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123470, d170475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123470, d170475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123471 q = 1) (hb : d170476 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123471, d170476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123471, d170476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123472 q = 1) (hb : d170477 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123472, d170477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123472, d170477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123473 q = 1) (hb : d170478 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123473, d170478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123473, d170478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49622 (p : Pattern) (ha : d123480 p = 1) (hb : d170484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123475 q = 1) (hb : d170479 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123475, d170479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49618 q ha hb
    | true =>
      simp only [d123475, d170479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48919 q hb ha
  have h2 (q : Pattern) (ha : d123476 q = 1) (hb : d170480 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123476, d170480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123476, d170480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123477 q = 1) (hb : d170481 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123477, d170481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123477, d170481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123478 q = 1) (hb : d170482 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123478, d170482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123478, d170482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123479 q = 1) (hb : d170483 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123479, d170483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123479, d170483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123480 q = 1) (hb : d170484 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123480, d170484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123480, d170484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49623 (p : Pattern) (ha : d123486 p = 1) (hb : d170490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123468 q = 1) (hb : d170473 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123468, d170473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49620 q ha hb
    | true =>
      simp only [d123468, d170473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123469 q = 1) (hb : d170474 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123469, d170474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123469, d170474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123481 q = 1) (hb : d170485 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123481, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49622 q ha hb
    | true =>
      simp only [d123481, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123482 q = 1) (hb : d170486 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123482, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123482, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123483 q = 1) (hb : d170487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123483, d170487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123483, d170487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123484 q = 1) (hb : d170488 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123484, d170488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123484, d170488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123485 q = 1) (hb : d170489 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123485, d170489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123485, d170489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123486 q = 1) (hb : d170490 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123486, d170490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123486, d170490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49624 (p : Pattern) (ha : d123507 p = 1) (hb : d170498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123448 q = 1) (hb : d170459 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123448, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49616 q ha hb
    | true =>
      simp only [d123448, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49618 q ha hb
  have h2 (q : Pattern) (ha : d123449 q = 1) (hb : d170460 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123449, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123449, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123450 q = 1) (hb : d170461 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123450, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123450, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123457 q = 1) (hb : d170462 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123457, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49618 q ha hb
    | true =>
      simp only [d123457, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48946 q hb ha
  have h5 (q : Pattern) (ha : d123458 q = 1) (hb : d170463 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123458, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123458, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123459 q = 1) (hb : d170464 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123459, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123459, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123460 q = 1) (hb : d170465 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123460, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123460, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123502 q = 1) (hb : d170493 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123502, d170493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49618 q ha hb
    | true =>
      simp only [d123502, d170493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46255 q hb ha
  have h9 (q : Pattern) (ha : d123503 q = 1) (hb : d170494 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123503, d170494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123503, d170494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123504 q = 1) (hb : d170495 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123504, d170495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123504, d170495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123505 q = 1) (hb : d170496 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123505, d170496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123505, d170496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123506 q = 1) (hb : d170497 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123506, d170497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123506, d170497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123507 q = 1) (hb : d170498 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123507, d170498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123507, d170498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro49625 (p : Pattern) (ha : d123513 p = 1) (hb : d170504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123508 q = 1) (hb : d170499 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123508, d170499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49624 q ha hb
    | true =>
      simp only [d123508, d170499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123509 q = 1) (hb : d170500 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123509, d170500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123509, d170500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123510 q = 1) (hb : d170501 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123510, d170501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123510, d170501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123511 q = 1) (hb : d170502 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123511, d170502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123511, d170502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123512 q = 1) (hb : d170503 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123512, d170503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123512, d170503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123513 q = 1) (hb : d170504 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123513, d170504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123513, d170504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49626 (p : Pattern) (ha : d123519 p = 1) (hb : d170510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123487 q = 1) (hb : d170491 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123487, d170491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49621 q ha hb
    | true =>
      simp only [d123487, d170491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49623 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123500 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123501 q = 1) (hb : d170492 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123501, d170492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123501, d170492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d123514 q = 1) (hb : d170505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123514, d170505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49625 q ha hb
    | true =>
      simp only [d123514, d170505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123515 q = 1) (hb : d170506 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123515, d170506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123515, d170506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123516 q = 1) (hb : d170507 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123516, d170507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123516, d170507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123517 q = 1) (hb : d170508 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123517, d170508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123517, d170508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123518 q = 1) (hb : d170509 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123518, d170509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123518, d170509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123519 q = 1) (hb : d170510 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123519, d170510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123519, d170510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro49627 (p : Pattern) (ha : d123499 p = 1) (hb : d170515 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123481 q = 1) (hb : d170485 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123481, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49622 q ha hb
    | true =>
      simp only [d123481, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123482 q = 1) (hb : d170486 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123482, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123482, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123496 q = 1) (hb : d170512 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123496, d170512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123496, d170512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123497 q = 1) (hb : d170513 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123497, d170513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123497, d170513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123498 q = 1) (hb : d170514 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123498, d170514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123498, d170514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123499 q = 1) (hb : d170515 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123499, d170515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123499, d170515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49628 (p : Pattern) (ha : d123526 p = 1) (hb : d170521 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123521 q = 1) (hb : d170516 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123521, d170516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49627 q ha hb
    | true =>
      simp only [d123521, d170516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123522 q = 1) (hb : d170517 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123522, d170517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123522, d170517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123523 q = 1) (hb : d170518 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123523, d170518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123523, d170518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123524 q = 1) (hb : d170519 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123524, d170519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123524, d170519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123525 q = 1) (hb : d170520 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123525, d170520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123525, d170520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123526 q = 1) (hb : d170521 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123526, d170521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123526, d170521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49629 (p : Pattern) (ha : d123532 p = 1) (hb : d170527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123283 q = 1) (hb : d170311 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123283, d170311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123283, d170311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49586 q ha hb
  have h2 (q : Pattern) (ha : d123284 q = 1) (hb : d170312 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123284, d170312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123284, d170312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123293 q = 1) (hb : d170321 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123293, d170321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49586 q ha hb
    | true =>
      simp only [d123293, d170321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49589 q ha hb
  have h4 (q : Pattern) (ha : d123294 q = 1) (hb : d170322 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123294, d170322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123294, d170322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123295 q = 1) (hb : d170323 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123295, d170323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123295, d170323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123386 q = 1) (hb : d170411 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123386, d170411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49602 q ha hb
    | true =>
      simp only [d123386, d170411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49610 q ha hb
  have h7 (q : Pattern) (ha : d123404 q = 1) (hb : d170429 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123404, d170429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49611 q ha hb
    | true =>
      simp only [d123404, d170429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49612 q ha hb
  have h8 (q : Pattern) (ha : d123405 q = 1) (hb : d170430 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123405, d170430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123405, d170430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123406 q = 1) (hb : d170431 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123406, d170431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123406, d170431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123407 q = 1) (hb : d170432 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123407, d170432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123407, d170432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123411 q = 1) (hb : d170436 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123411, d170436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123411, d170436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49613 q ha hb
  have h12 (q : Pattern) (ha : d123413 q = 1) (hb : d170438 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123413, d170438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123413, d170438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49614 q ha hb
  have h13 (q : Pattern) (ha : d123414 q = 1) (hb : d170439 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123414, d170439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123414, d170439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123415 q = 1) (hb : d170440 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123415, d170440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123415, d170440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d123416 q = 1) (hb : d170441 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123416, d170441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d123416, d170441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d123417 q = 1) (hb : d170442 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123417, d170442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123417, d170442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d123520 q = 1) (hb : d170511 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123520, d170511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123520, d170511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49626 q ha hb
  have h18 (q : Pattern) (ha : d123527 q = 1) (hb : d170522 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123527, d170522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123527, d170522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49628 q ha hb
  have h19 (q : Pattern) (ha : d123528 q = 1) (hb : d170523 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123528, d170523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123528, d170523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d123529 q = 1) (hb : d170524 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123529, d170524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d123529, d170524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d123530 q = 1) (hb : d170525 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123530, d170525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d123530, d170525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d123531 q = 1) (hb : d170526 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123531, d170526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d123531, d170526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d123532 q = 1) (hb : d170527 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d123532, d170527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d123532, d170527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro49630 (p : Pattern) (ha : d123538 p = 1) (hb : d170533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123533 q = 1) (hb : d170528 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d123533, d170528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123533, d170528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49629 q ha hb
  have h2 (q : Pattern) (ha : d123534 q = 1) (hb : d170529 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d123534, d170529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123534, d170529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123535 q = 1) (hb : d170530 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d123535, d170530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123535, d170530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123536 q = 1) (hb : d170531 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d123536, d170531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123536, d170531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123537 q = 1) (hb : d170532 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d123537, d170532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123537, d170532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123538 q = 1) (hb : d170533 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d123538, d170533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123538, d170533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49631 (p : Pattern) (ha : d123545 p = 1) (hb : d170539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10343 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46271 q ha hb
    | true =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10345 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17225 q = 1) (hb : d53316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17225, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17225, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17226 q = 1) (hb : d53317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17226, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17226, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d123543 q = 1) (hb : d170538 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123543, d170538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123543, d170538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13675 q = 1) (hb : d113865 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13676 q = 1) (hb : d113866 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15545 q = 1) (hb : d123544 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15545, d123544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15545, d123544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d123545 q = 1) (hb : d170539 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123545, d170539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123545, d170539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro49632 (p : Pattern) (ha : d123550 p = 1) (hb : d170541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10364 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46267 q ha hb
    | true =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10366 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17153 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17153, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17154 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17154, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17154, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d123546 q = 1) (hb : d170540 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123546, d170540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123546, d170540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d13678 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33547 q ha hb
    | true =>
      simp only [d13678, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13679 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13679, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13680 q = 1) (hb : d123547 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, d123547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13680, d123547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13681 q = 1) (hb : d123548 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, d123548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13681, d123548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d22693 q = 1) (hb : d123549 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22693, d123549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22693, d123549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d123550 q = 1) (hb : d170541 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123550, d170541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123550, d170541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro49633 (p : Pattern) (ha : d123568 p = 1) (hb : d170554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123551 q = 1) (hb : d170542 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123551, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49631 q ha hb
    | true =>
      simp only [d123551, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49632 q ha hb
  have h2 (q : Pattern) (ha : d123552 q = 1) (hb : d170543 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123552, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123552, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123553 q = 1) (hb : d170544 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123553, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123553, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123558 q = 1) (hb : d170545 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123558, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49632 q ha hb
    | true =>
      simp only [d123558, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48958 q hb ha
  have h5 (q : Pattern) (ha : d123559 q = 1) (hb : d170546 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123559, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123559, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123560 q = 1) (hb : d170547 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123560, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123560, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123561 q = 1) (hb : d170548 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123561, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123561, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123563 q = 1) (hb : d170549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123563, d170549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49632 q ha hb
    | true =>
      simp only [d123563, d170549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48959 q hb ha
  have h9 (q : Pattern) (ha : d123564 q = 1) (hb : d170550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123564, d170550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123564, d170550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123565 q = 1) (hb : d170551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123565, d170551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123565, d170551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123566 q = 1) (hb : d170552 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123566, d170552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123566, d170552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123567 q = 1) (hb : d170553 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123567, d170553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123567, d170553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123568 q = 1) (hb : d170554 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123568, d170554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123568, d170554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro49634 (p : Pattern) (ha : d123572 p = 1) (hb : d170558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123563 q = 1) (hb : d170549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123563, d170549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49632 q ha hb
    | true =>
      simp only [d123563, d170549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48959 q hb ha
  have h2 (q : Pattern) (ha : d123564 q = 1) (hb : d170550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123564, d170550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123564, d170550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123565 q = 1) (hb : d170551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123565, d170551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123565, d170551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123566 q = 1) (hb : d170552 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123566, d170552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123566, d170552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123571 q = 1) (hb : d170557 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123571, d170557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123571, d170557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123572 q = 1) (hb : d170558 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123572, d170558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123572, d170558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49635 (p : Pattern) (ha : d123578 p = 1) (hb : d170564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123569 q = 1) (hb : d170555 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123569, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49633 q ha hb
    | true =>
      simp only [d123569, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123570 q = 1) (hb : d170556 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123570, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123570, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123573 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49634 q ha hb
    | true =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123574 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123575 q = 1) (hb : d170561 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123575, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123575, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123576 q = 1) (hb : d170562 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123576, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123576, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123577 q = 1) (hb : d170563 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123577, d170563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123577, d170563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123578 q = 1) (hb : d170564 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123578, d170564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123578, d170564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49636 (p : Pattern) (ha : d123582 p = 1) (hb : d170568 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123573 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49634 q ha hb
    | true =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123574 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123579 q = 1) (hb : d170565 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123579, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123579, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123580 q = 1) (hb : d170566 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123580, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123580, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123581 q = 1) (hb : d170567 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123581, d170567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123581, d170567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123582 q = 1) (hb : d170568 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123582, d170568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123582, d170568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49637 (p : Pattern) (ha : d123588 p = 1) (hb : d170574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123583 q = 1) (hb : d170569 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123583, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49635 q ha hb
    | true =>
      simp only [d123583, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49636 q ha hb
  have h2 (q : Pattern) (ha : d123584 q = 1) (hb : d170570 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123584, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123584, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123585 q = 1) (hb : d170571 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123585, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123585, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123586 q = 1) (hb : d170572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123586, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123586, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123587 q = 1) (hb : d170573 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123587, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123587, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123588 q = 1) (hb : d170574 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123588, d170574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123588, d170574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49638 (p : Pattern) (ha : d123591 p = 1) (hb : d170577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123569 q = 1) (hb : d170555 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123569, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49633 q ha hb
    | true =>
      simp only [d123569, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123570 q = 1) (hb : d170556 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123570, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123570, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123573 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49634 q ha hb
    | true =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123574 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123575 q = 1) (hb : d170561 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123575, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123575, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123576 q = 1) (hb : d170562 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123576, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123576, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123577 q = 1) (hb : d170563 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123577, d170563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123577, d170563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123591 q = 1) (hb : d170577 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123591, d170577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123591, d170577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49639 (p : Pattern) (ha : d123592 p = 1) (hb : d170578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123573 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49634 q ha hb
    | true =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123574 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123579 q = 1) (hb : d170565 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123579, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123579, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123580 q = 1) (hb : d170566 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123580, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123580, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123581 q = 1) (hb : d170567 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123581, d170567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123581, d170567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123592 q = 1) (hb : d170578 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123592, d170578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123592, d170578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49640 (p : Pattern) (ha : d123598 p = 1) (hb : d170584 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123583 q = 1) (hb : d170569 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123583, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49635 q ha hb
    | true =>
      simp only [d123583, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49636 q ha hb
  have h2 (q : Pattern) (ha : d123584 q = 1) (hb : d170570 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123584, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123584, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123585 q = 1) (hb : d170571 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123585, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123585, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123586 q = 1) (hb : d170572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123586, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123586, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123587 q = 1) (hb : d170573 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123587, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123587, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123593 q = 1) (hb : d170579 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123593, d170579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49638 q ha hb
    | true =>
      simp only [d123593, d170579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49639 q ha hb
  have h7 (q : Pattern) (ha : d123594 q = 1) (hb : d170580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123594, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123594, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123595 q = 1) (hb : d170581 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123595, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123595, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123596 q = 1) (hb : d170582 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123596, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123596, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123597 q = 1) (hb : d170583 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123597, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123597, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123598 q = 1) (hb : d170584 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123598, d170584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123598, d170584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49641 (p : Pattern) (ha : d123603 p = 1) (hb : d170589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123569 q = 1) (hb : d170555 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123569, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49633 q ha hb
    | true =>
      simp only [d123569, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123570 q = 1) (hb : d170556 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123570, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123570, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123573 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49634 q ha hb
    | true =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123574 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123575 q = 1) (hb : d170561 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123575, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123575, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123576 q = 1) (hb : d170562 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123576, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123576, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123602 q = 1) (hb : d170588 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123602, d170588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123602, d170588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123603 q = 1) (hb : d170589 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123603, d170589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123603, d170589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49642 (p : Pattern) (ha : d123605 p = 1) (hb : d170591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123573 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49634 q ha hb
    | true =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123574 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123579 q = 1) (hb : d170565 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123579, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123579, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123580 q = 1) (hb : d170566 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123580, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123580, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123604 q = 1) (hb : d170590 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123604, d170590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123604, d170590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123605 q = 1) (hb : d170591 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123605, d170591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123605, d170591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49643 (p : Pattern) (ha : d123612 p = 1) (hb : d170598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123569 q = 1) (hb : d170555 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123569, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49633 q ha hb
    | true =>
      simp only [d123569, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123570 q = 1) (hb : d170556 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123570, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123570, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123573 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49634 q ha hb
    | true =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123574 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123575 q = 1) (hb : d170561 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123575, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123575, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123610 q = 1) (hb : d170596 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123610, d170596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123610, d170596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123611 q = 1) (hb : d170597 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123611, d170597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123611, d170597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123612 q = 1) (hb : d170598 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123612, d170598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123612, d170598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49644 (p : Pattern) (ha : d123615 p = 1) (hb : d170601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123573 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49634 q ha hb
    | true =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123574 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123579 q = 1) (hb : d170565 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123579, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123579, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123613 q = 1) (hb : d170599 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123613, d170599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123613, d170599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123614 q = 1) (hb : d170600 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123614, d170600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123614, d170600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123615 q = 1) (hb : d170601 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123615, d170601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123615, d170601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49645 (p : Pattern) (ha : d123624 p = 1) (hb : d170608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13675 q = 1) (hb : d113865 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13676 q = 1) (hb : d113866 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15545 q = 1) (hb : d123544 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15545, d123544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15545, d123544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13678 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33547 q ha hb
    | true =>
      simp only [d13678, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13679 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13679, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13680 q = 1) (hb : d123547 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, d123547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13680, d123547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13681 q = 1) (hb : d123548 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, d123548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13681, d123548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d22693 q = 1) (hb : d123549 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22693, d123549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22693, d123549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d123624 q = 1) (hb : d170608 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123624, d170608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d123624, d170608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro49646 (p : Pattern) (ha : d123630 p = 1) (hb : d170614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123620 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d123621 q = 1) (hb : d170605 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123621, d170605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123621, d170605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49631 q ha hb
  have h3 (q : Pattern) (ha : d123622 q = 1) (hb : d170606 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123622, d170606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123622, d170606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123623 q = 1) (hb : d170607 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123623, d170607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123623, d170607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123625 q = 1) (hb : d170609 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123625, d170609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49631 q ha hb
    | true =>
      simp only [d123625, d170609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49645 q ha hb
  have h6 (q : Pattern) (ha : d123626 q = 1) (hb : d170610 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123626, d170610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123626, d170610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123627 q = 1) (hb : d170611 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123627, d170611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123627, d170611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123628 q = 1) (hb : d170612 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123628, d170612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123628, d170612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123551 q = 1) (hb : d170542 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123551, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49631 q ha hb
    | true =>
      simp only [d123551, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49632 q ha hb
  have h10 (q : Pattern) (ha : d123552 q = 1) (hb : d170543 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123552, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123552, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123553 q = 1) (hb : d170544 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123553, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123553, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d123558 q = 1) (hb : d170545 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123558, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49632 q ha hb
    | true =>
      simp only [d123558, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48958 q hb ha
  have h13 (q : Pattern) (ha : d123559 q = 1) (hb : d170546 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123559, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123559, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123560 q = 1) (hb : d170547 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123560, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123560, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123561 q = 1) (hb : d170548 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123561, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123561, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123629 q = 1) (hb : d170613 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123629, d170613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123629, d170613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d123630 q = 1) (hb : d170614 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123630, d170614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d123630, d170614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro49647 (p : Pattern) (ha : d123635 p = 1) (hb : d170619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123551 q = 1) (hb : d170542 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123551, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49631 q ha hb
    | true =>
      simp only [d123551, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49632 q ha hb
  have h2 (q : Pattern) (ha : d123552 q = 1) (hb : d170543 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123552, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123552, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123553 q = 1) (hb : d170544 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123553, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123553, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123558 q = 1) (hb : d170545 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123558, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49632 q ha hb
    | true =>
      simp only [d123558, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48958 q hb ha
  have h5 (q : Pattern) (ha : d123559 q = 1) (hb : d170546 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123559, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123559, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123560 q = 1) (hb : d170547 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123560, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123560, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123561 q = 1) (hb : d170548 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123561, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123561, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123633 q = 1) (hb : d170617 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123633, d170617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123633, d170617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123634 q = 1) (hb : d170618 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123634, d170618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123634, d170618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123635 q = 1) (hb : d170619 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123635, d170619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d123635, d170619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro49648 (p : Pattern) (ha : d123641 p = 1) (hb : d170625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123631 q = 1) (hb : d170615 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123631, d170615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49646 q ha hb
    | true =>
      simp only [d123631, d170615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123632 q = 1) (hb : d170616 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123632, d170616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123632, d170616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123636 q = 1) (hb : d170620 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123636, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49647 q ha hb
    | true =>
      simp only [d123636, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123637 q = 1) (hb : d170621 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123637, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123637, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123638 q = 1) (hb : d170622 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123638, d170622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123638, d170622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123639 q = 1) (hb : d170623 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123639, d170623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123639, d170623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123640 q = 1) (hb : d170624 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123640, d170624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123640, d170624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123641 q = 1) (hb : d170625 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123641, d170625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123641, d170625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49649 (p : Pattern) (ha : d123645 p = 1) (hb : d170629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123636 q = 1) (hb : d170620 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123636, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49647 q ha hb
    | true =>
      simp only [d123636, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123637 q = 1) (hb : d170621 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123637, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123637, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123573 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49634 q ha hb
    | true =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123574 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123642 q = 1) (hb : d170626 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123642, d170626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123642, d170626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123643 q = 1) (hb : d170627 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123643, d170627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123643, d170627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123644 q = 1) (hb : d170628 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123644, d170628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123644, d170628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123645 q = 1) (hb : d170629 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123645, d170629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123645, d170629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49650 (p : Pattern) (ha : d123653 p = 1) (hb : d170637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123551 q = 1) (hb : d170542 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123551, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49631 q ha hb
    | true =>
      simp only [d123551, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49632 q ha hb
  have h2 (q : Pattern) (ha : d123552 q = 1) (hb : d170543 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123552, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123552, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123553 q = 1) (hb : d170544 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123553, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123553, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123558 q = 1) (hb : d170545 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123558, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49632 q ha hb
    | true =>
      simp only [d123558, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48958 q hb ha
  have h5 (q : Pattern) (ha : d123559 q = 1) (hb : d170546 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123559, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123559, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123560 q = 1) (hb : d170547 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123560, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123560, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123561 q = 1) (hb : d170548 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123561, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123561, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123648 q = 1) (hb : d170632 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123648, d170632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49632 q ha hb
    | true =>
      simp only [d123648, d170632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46266 q hb ha
  have h9 (q : Pattern) (ha : d123649 q = 1) (hb : d170633 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123649, d170633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123649, d170633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123650 q = 1) (hb : d170634 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123650, d170634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123650, d170634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123651 q = 1) (hb : d170635 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123651, d170635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123651, d170635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123652 q = 1) (hb : d170636 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123652, d170636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123652, d170636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123653 q = 1) (hb : d170637 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123653, d170637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123653, d170637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro49651 (p : Pattern) (ha : d123659 p = 1) (hb : d170643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123654 q = 1) (hb : d170638 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123654, d170638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49650 q ha hb
    | true =>
      simp only [d123654, d170638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123655 q = 1) (hb : d170639 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123655, d170639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123655, d170639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123656 q = 1) (hb : d170640 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123656, d170640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123656, d170640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123657 q = 1) (hb : d170641 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123657, d170641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123657, d170641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123658 q = 1) (hb : d170642 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123658, d170642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123658, d170642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123659 q = 1) (hb : d170643 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123659, d170643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123659, d170643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49652 (p : Pattern) (ha : d123665 p = 1) (hb : d170649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123606 q = 1) (hb : d170592 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123606, d170592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49641 q ha hb
    | true =>
      simp only [d123606, d170592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49642 q ha hb
  have h2 (q : Pattern) (ha : d123607 q = 1) (hb : d170593 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123607, d170593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123607, d170593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123608 q = 1) (hb : d170594 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123608, d170594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123608, d170594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123609 q = 1) (hb : d170595 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123609, d170595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123609, d170595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123616 q = 1) (hb : d170602 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123616, d170602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49643 q ha hb
    | true =>
      simp only [d123616, d170602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49644 q ha hb
  have h6 (q : Pattern) (ha : d123617 q = 1) (hb : d170603 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123617, d170603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123617, d170603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123618 q = 1) (hb : d170604 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123618, d170604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123618, d170604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123646 q = 1) (hb : d170630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123646, d170630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49648 q ha hb
    | true =>
      simp only [d123646, d170630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49649 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123583 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d123647 q = 1) (hb : d170631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123647, d170631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123647, d170631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d123660 q = 1) (hb : d170644 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123660, d170644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49651 q ha hb
    | true =>
      simp only [d123660, d170644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123661 q = 1) (hb : d170645 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123661, d170645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123661, d170645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d123662 q = 1) (hb : d170646 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123662, d170646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123662, d170646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123663 q = 1) (hb : d170647 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123663, d170647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123663, d170647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123664 q = 1) (hb : d170648 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123664, d170648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123664, d170648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123665 q = 1) (hb : d170649 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123665, d170649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123665, d170649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro49653 (p : Pattern) (ha : d123666 p = 1) (hb : d170650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123569 q = 1) (hb : d170555 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123569, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49633 q ha hb
    | true =>
      simp only [d123569, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123570 q = 1) (hb : d170556 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123570, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123570, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123573 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49634 q ha hb
    | true =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123574 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123575 q = 1) (hb : d170561 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123575, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123575, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123576 q = 1) (hb : d170562 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123576, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123576, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123602 q = 1) (hb : d170588 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123602, d170588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123602, d170588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123666 q = 1) (hb : d170650 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123666, d170650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123666, d170650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49654 (p : Pattern) (ha : d123667 p = 1) (hb : d170651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123573 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49634 q ha hb
    | true =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123574 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123579 q = 1) (hb : d170565 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123579, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123579, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123580 q = 1) (hb : d170566 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123580, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123580, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123604 q = 1) (hb : d170590 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123604, d170590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123604, d170590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123667 q = 1) (hb : d170651 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123667, d170651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123667, d170651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49655 (p : Pattern) (ha : d123672 p = 1) (hb : d170656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123569 q = 1) (hb : d170555 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123569, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49633 q ha hb
    | true =>
      simp only [d123569, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123570 q = 1) (hb : d170556 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123570, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123570, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123573 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49634 q ha hb
    | true =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123574 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123575 q = 1) (hb : d170561 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123575, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123575, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123610 q = 1) (hb : d170596 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123610, d170596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123610, d170596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123611 q = 1) (hb : d170597 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123611, d170597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123611, d170597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123672 q = 1) (hb : d170656 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123672, d170656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123672, d170656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49656 (p : Pattern) (ha : d123673 p = 1) (hb : d170657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123573 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49634 q ha hb
    | true =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123574 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123579 q = 1) (hb : d170565 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123579, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123579, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123613 q = 1) (hb : d170599 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123613, d170599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123613, d170599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123614 q = 1) (hb : d170600 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123614, d170600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123614, d170600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123673 q = 1) (hb : d170657 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123673, d170657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123673, d170657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49657 (p : Pattern) (ha : d123677 p = 1) (hb : d170661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123631 q = 1) (hb : d170615 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123631, d170615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49646 q ha hb
    | true =>
      simp only [d123631, d170615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123632 q = 1) (hb : d170616 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123632, d170616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123632, d170616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123636 q = 1) (hb : d170620 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123636, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49647 q ha hb
    | true =>
      simp only [d123636, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123637 q = 1) (hb : d170621 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123637, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123637, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123638 q = 1) (hb : d170622 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123638, d170622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123638, d170622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123639 q = 1) (hb : d170623 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123639, d170623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123639, d170623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123640 q = 1) (hb : d170624 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123640, d170624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123640, d170624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123677 q = 1) (hb : d170661 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123677, d170661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123677, d170661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49658 (p : Pattern) (ha : d123678 p = 1) (hb : d170662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123636 q = 1) (hb : d170620 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123636, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49647 q ha hb
    | true =>
      simp only [d123636, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123637 q = 1) (hb : d170621 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123637, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123637, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123573 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49634 q ha hb
    | true =>
      simp only [d123573, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123574 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123574, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123642 q = 1) (hb : d170626 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123642, d170626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123642, d170626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123643 q = 1) (hb : d170627 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123643, d170627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123643, d170627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123644 q = 1) (hb : d170628 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123644, d170628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123644, d170628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123678 q = 1) (hb : d170662 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123678, d170662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123678, d170662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49659 (p : Pattern) (ha : d123681 p = 1) (hb : d170665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123654 q = 1) (hb : d170638 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123654, d170638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49650 q ha hb
    | true =>
      simp only [d123654, d170638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123655 q = 1) (hb : d170639 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123655, d170639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123655, d170639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123656 q = 1) (hb : d170640 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123656, d170640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123656, d170640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123657 q = 1) (hb : d170641 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123657, d170641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123657, d170641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123658 q = 1) (hb : d170642 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123658, d170642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123658, d170642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123681 q = 1) (hb : d170665 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123681, d170665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123681, d170665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49660 (p : Pattern) (ha : d123687 p = 1) (hb : d170671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123606 q = 1) (hb : d170592 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123606, d170592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49641 q ha hb
    | true =>
      simp only [d123606, d170592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49642 q ha hb
  have h2 (q : Pattern) (ha : d123607 q = 1) (hb : d170593 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123607, d170593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123607, d170593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123608 q = 1) (hb : d170594 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123608, d170594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123608, d170594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123609 q = 1) (hb : d170595 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123609, d170595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123609, d170595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123616 q = 1) (hb : d170602 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123616, d170602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49643 q ha hb
    | true =>
      simp only [d123616, d170602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49644 q ha hb
  have h6 (q : Pattern) (ha : d123617 q = 1) (hb : d170603 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123617, d170603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123617, d170603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123618 q = 1) (hb : d170604 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123618, d170604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123618, d170604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123646 q = 1) (hb : d170630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123646, d170630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49648 q ha hb
    | true =>
      simp only [d123646, d170630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49649 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123583 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d123647 q = 1) (hb : d170631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123647, d170631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123647, d170631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d123660 q = 1) (hb : d170644 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123660, d170644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49651 q ha hb
    | true =>
      simp only [d123660, d170644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123661 q = 1) (hb : d170645 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123661, d170645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123661, d170645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d123662 q = 1) (hb : d170646 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123662, d170646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123662, d170646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123663 q = 1) (hb : d170647 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123663, d170647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123663, d170647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123664 q = 1) (hb : d170648 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123664, d170648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123664, d170648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123668 q = 1) (hb : d170652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123668, d170652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49653 q ha hb
    | true =>
      simp only [d123668, d170652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49654 q ha hb
  have h17 (q : Pattern) (ha : d123669 q = 1) (hb : d170653 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123669, d170653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123669, d170653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d123670 q = 1) (hb : d170654 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123670, d170654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123670, d170654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d123671 q = 1) (hb : d170655 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123671, d170655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123671, d170655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d123674 q = 1) (hb : d170658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123674, d170658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49655 q ha hb
    | true =>
      simp only [d123674, d170658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49656 q ha hb
  have h21 (q : Pattern) (ha : d123675 q = 1) (hb : d170659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123675, d170659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123675, d170659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d123676 q = 1) (hb : d170660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123676, d170660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d123676, d170660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d123679 q = 1) (hb : d170663 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123679, d170663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49657 q ha hb
    | true =>
      simp only [d123679, d170663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49658 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d123593 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d123680 q = 1) (hb : d170664 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123680, d170664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d123680, d170664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d123682 q = 1) (hb : d170666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123682, d170666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49659 q ha hb
    | true =>
      simp only [d123682, d170666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d123683 q = 1) (hb : d170667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123683, d170667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d123683, d170667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d123684 q = 1) (hb : d170668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123684, d170668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d123684, d170668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d123685 q = 1) (hb : d170669 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123685, d170669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d123685, d170669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d123686 q = 1) (hb : d170670 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123686, d170670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d123686, d170670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d123687 q = 1) (hb : d170671 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123687, d170671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123687, d170671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro49661 (p : Pattern) (ha : d123699 p = 1) (hb : d170683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123689 q = 1) (hb : d170673 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123689, d170673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49649 q ha hb
    | true =>
      simp only [d123689, d170673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49636 q ha hb
  have h2 (q : Pattern) (ha : d123690 q = 1) (hb : d170674 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123690, d170674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123690, d170674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123691 q = 1) (hb : d170675 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123691, d170675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123691, d170675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123692 q = 1) (hb : d170676 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123692, d170676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123692, d170676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123693 q = 1) (hb : d170677 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123693, d170677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123693, d170677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123694 q = 1) (hb : d170678 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123694, d170678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49636 q ha hb
    | true =>
      simp only [d123694, d170678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123695 q = 1) (hb : d170679 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123695, d170679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123695, d170679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123696 q = 1) (hb : d170680 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123696, d170680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123696, d170680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123697 q = 1) (hb : d170681 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123697, d170681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123697, d170681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123698 q = 1) (hb : d170682 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123698, d170682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123698, d170682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123699 q = 1) (hb : d170683 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123699, d170683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123699, d170683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49662 (p : Pattern) (ha : d123705 p = 1) (hb : d170689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123694 q = 1) (hb : d170678 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123694, d170678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49636 q ha hb
    | true =>
      simp only [d123694, d170678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123695 q = 1) (hb : d170679 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123695, d170679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123695, d170679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123696 q = 1) (hb : d170680 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123696, d170680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123696, d170680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123697 q = 1) (hb : d170681 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123697, d170681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123697, d170681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123698 q = 1) (hb : d170682 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123698, d170682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123698, d170682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123700 q = 1) (hb : d170684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123700, d170684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49639 q ha hb
    | true =>
      simp only [d123700, d170684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123701 q = 1) (hb : d170685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123701, d170685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123701, d170685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123702 q = 1) (hb : d170686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123702, d170686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123702, d170686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123703 q = 1) (hb : d170687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123703, d170687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123703, d170687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123704 q = 1) (hb : d170688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123704, d170688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123704, d170688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123705 q = 1) (hb : d170689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123705, d170689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123705, d170689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49663 (p : Pattern) (ha : d123712 p = 1) (hb : d170696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123679 q = 1) (hb : d170663 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123679, d170663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49657 q ha hb
    | true =>
      simp only [d123679, d170663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49658 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123593 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123680 q = 1) (hb : d170664 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123680, d170664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123680, d170664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d123682 q = 1) (hb : d170666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123682, d170666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49659 q ha hb
    | true =>
      simp only [d123682, d170666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123683 q = 1) (hb : d170667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123683, d170667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123683, d170667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123684 q = 1) (hb : d170668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123684, d170668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123684, d170668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123710 q = 1) (hb : d170694 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123710, d170694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123710, d170694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123711 q = 1) (hb : d170695 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123711, d170695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123711, d170695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123712 q = 1) (hb : d170696 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123712, d170696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123712, d170696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro49664 (p : Pattern) (ha : d123714 p = 1) (hb : d170698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123700 q = 1) (hb : d170684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123700, d170684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49639 q ha hb
    | true =>
      simp only [d123700, d170684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123701 q = 1) (hb : d170685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123701, d170685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123701, d170685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123702 q = 1) (hb : d170686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123702, d170686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123702, d170686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123703 q = 1) (hb : d170687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123703, d170687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123703, d170687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123704 q = 1) (hb : d170688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123704, d170688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123704, d170688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123714 q = 1) (hb : d170698 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123714, d170698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123714, d170698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49665 (p : Pattern) (ha : d123724 p = 1) (hb : d170705 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17369 q = 1) (hb : d53500 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17369, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46271 q ha hb
  have h2 (q : Pattern) (ha : d10343 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46271 q ha hb
    | true =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17370 q = 1) (hb : d53501 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17370, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17370, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10345 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17371 q = 1) (hb : d53502 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17371, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17371, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17372 q = 1) (hb : d53503 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17372, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17372, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d123722 q = 1) (hb : d170704 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123722, d170704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d123722, d170704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h9 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13814 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13815 q = 1) (hb : d113967 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13816 q = 1) (hb : d113968 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15770 q = 1) (hb : d123723 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15770, d123723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15770, d123723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d123724 q = 1) (hb : d170705 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123724, d170705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123724, d170705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro49666 (p : Pattern) (ha : d123733 p = 1) (hb : d170709 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h2 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13814 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13815 q = 1) (hb : d113967 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13816 q = 1) (hb : d113968 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15770 q = 1) (hb : d123723 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15770, d123723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15770, d123723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13817 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13817, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33547 q ha hb
  have h9 (q : Pattern) (ha : d13678 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33547 q ha hb
    | true =>
      simp only [d13678, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13818 q = 1) (hb : d123729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13818, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13679 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13679, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13819 q = 1) (hb : d123730 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13819, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13820 q = 1) (hb : d123731 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13820, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d22937 q = 1) (hb : d123732 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22937, d123732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22937, d123732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d123733 q = 1) (hb : d170709 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123733, d170709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d123733, d170709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro49667 (p : Pattern) (ha : d123739 p = 1) (hb : d170715 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17376 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17376, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46267 q ha hb
  have h2 (q : Pattern) (ha : d10364 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46267 q ha hb
    | true =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17377 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17377, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10366 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17378 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17378, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17378, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17379 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17379, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17379, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d123738 q = 1) (hb : d170714 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123738, d170714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d123738, d170714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d13817 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13817, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33547 q ha hb
  have h9 (q : Pattern) (ha : d13678 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33547 q ha hb
    | true =>
      simp only [d13678, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13818 q = 1) (hb : d123729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13818, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13679 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13679, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13819 q = 1) (hb : d123730 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13819, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13820 q = 1) (hb : d123731 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13820, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d22937 q = 1) (hb : d123732 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22937, d123732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22937, d123732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d123739 q = 1) (hb : d170715 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123739, d170715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123739, d170715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro49668 (p : Pattern) (ha : d123754 p = 1) (hb : d170724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d123725 q = 1) (hb : d170706 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123725, d170706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123725, d170706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49665 q ha hb
  have h3 (q : Pattern) (ha : d123726 q = 1) (hb : d170707 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123726, d170707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123726, d170707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123727 q = 1) (hb : d170708 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123727, d170708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123727, d170708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123734 q = 1) (hb : d170710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123734, d170710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49665 q ha hb
    | true =>
      simp only [d123734, d170710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49666 q ha hb
  have h6 (q : Pattern) (ha : d123735 q = 1) (hb : d170711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123735, d170711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123735, d170711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123736 q = 1) (hb : d170712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123736, d170712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123736, d170712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123737 q = 1) (hb : d170713 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123737, d170713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123737, d170713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123740 q = 1) (hb : d170716 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123740, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49665 q ha hb
    | true =>
      simp only [d123740, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49667 q ha hb
  have h10 (q : Pattern) (ha : d123741 q = 1) (hb : d170717 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123741, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123741, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123742 q = 1) (hb : d170718 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123742, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123742, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d123749 q = 1) (hb : d170719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123749, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49667 q ha hb
    | true =>
      simp only [d123749, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49001 q hb ha
  have h13 (q : Pattern) (ha : d123750 q = 1) (hb : d170720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123750, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123750, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123751 q = 1) (hb : d170721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123751, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123751, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123752 q = 1) (hb : d170722 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123752, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123752, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123753 q = 1) (hb : d170723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123753, d170723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123753, d170723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d123754 q = 1) (hb : d170724 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123754, d170724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d123754, d170724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro49669 (p : Pattern) (ha : d123759 p = 1) (hb : d170729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123740 q = 1) (hb : d170716 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123740, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49665 q ha hb
    | true =>
      simp only [d123740, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49667 q ha hb
  have h2 (q : Pattern) (ha : d123741 q = 1) (hb : d170717 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123741, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123741, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123742 q = 1) (hb : d170718 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123742, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123742, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123749 q = 1) (hb : d170719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123749, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49667 q ha hb
    | true =>
      simp only [d123749, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49001 q hb ha
  have h5 (q : Pattern) (ha : d123750 q = 1) (hb : d170720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123750, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123750, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123751 q = 1) (hb : d170721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123751, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123751, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123752 q = 1) (hb : d170722 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123752, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123752, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123757 q = 1) (hb : d170727 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123757, d170727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123757, d170727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d123758 q = 1) (hb : d170728 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123758, d170728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123758, d170728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123759 q = 1) (hb : d170729 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123759, d170729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d123759, d170729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro49670 (p : Pattern) (ha : d123765 p = 1) (hb : d170735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123755 q = 1) (hb : d170725 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123755, d170725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49668 q ha hb
    | true =>
      simp only [d123755, d170725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123756 q = 1) (hb : d170726 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123756, d170726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123756, d170726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123760 q = 1) (hb : d170730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123760, d170730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49669 q ha hb
    | true =>
      simp only [d123760, d170730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123761 q = 1) (hb : d170731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123761, d170731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123761, d170731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123762 q = 1) (hb : d170732 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123762, d170732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123762, d170732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123763 q = 1) (hb : d170733 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123763, d170733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123763, d170733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123764 q = 1) (hb : d170734 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123764, d170734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123764, d170734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123765 q = 1) (hb : d170735 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123765, d170735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123765, d170735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49671 (p : Pattern) (ha : d123772 p = 1) (hb : d170741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123767 q = 1) (hb : d170736 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123767, d170736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49667 q ha hb
    | true =>
      simp only [d123767, d170736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48974 q hb ha
  have h2 (q : Pattern) (ha : d123768 q = 1) (hb : d170737 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123768, d170737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123768, d170737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123769 q = 1) (hb : d170738 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123769, d170738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123769, d170738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123770 q = 1) (hb : d170739 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123770, d170739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123770, d170739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123771 q = 1) (hb : d170740 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123771, d170740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123771, d170740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123772 q = 1) (hb : d170741 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123772, d170741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123772, d170741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49672 (p : Pattern) (ha : d123778 p = 1) (hb : d170747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123760 q = 1) (hb : d170730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123760, d170730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49669 q ha hb
    | true =>
      simp only [d123760, d170730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123761 q = 1) (hb : d170731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123761, d170731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123761, d170731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123773 q = 1) (hb : d170742 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123773, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49671 q ha hb
    | true =>
      simp only [d123773, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123774 q = 1) (hb : d170743 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123774, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123774, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123775 q = 1) (hb : d170744 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123775, d170744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123775, d170744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123776 q = 1) (hb : d170745 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123776, d170745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123776, d170745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123777 q = 1) (hb : d170746 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123777, d170746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123777, d170746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123778 q = 1) (hb : d170747 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123778, d170747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123778, d170747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49673 (p : Pattern) (ha : d123799 p = 1) (hb : d170755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123740 q = 1) (hb : d170716 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123740, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49665 q ha hb
    | true =>
      simp only [d123740, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49667 q ha hb
  have h2 (q : Pattern) (ha : d123741 q = 1) (hb : d170717 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123741, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123741, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123742 q = 1) (hb : d170718 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123742, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123742, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123749 q = 1) (hb : d170719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123749, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49667 q ha hb
    | true =>
      simp only [d123749, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49001 q hb ha
  have h5 (q : Pattern) (ha : d123750 q = 1) (hb : d170720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123750, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123750, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123751 q = 1) (hb : d170721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123751, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123751, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123752 q = 1) (hb : d170722 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123752, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123752, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123794 q = 1) (hb : d170750 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123794, d170750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49667 q ha hb
    | true =>
      simp only [d123794, d170750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46313 q hb ha
  have h9 (q : Pattern) (ha : d123795 q = 1) (hb : d170751 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123795, d170751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123795, d170751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123796 q = 1) (hb : d170752 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123796, d170752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123796, d170752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123797 q = 1) (hb : d170753 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123797, d170753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123797, d170753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123798 q = 1) (hb : d170754 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123798, d170754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123798, d170754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123799 q = 1) (hb : d170755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123799, d170755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123799, d170755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro49674 (p : Pattern) (ha : d123805 p = 1) (hb : d170761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123800 q = 1) (hb : d170756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123800, d170756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49673 q ha hb
    | true =>
      simp only [d123800, d170756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123801 q = 1) (hb : d170757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123801, d170757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123801, d170757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123802 q = 1) (hb : d170758 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123802, d170758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123802, d170758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123803 q = 1) (hb : d170759 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123803, d170759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123803, d170759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123804 q = 1) (hb : d170760 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123804, d170760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123804, d170760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123805 q = 1) (hb : d170761 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123805, d170761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123805, d170761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49675 (p : Pattern) (ha : d123811 p = 1) (hb : d170767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123779 q = 1) (hb : d170748 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123779, d170748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49670 q ha hb
    | true =>
      simp only [d123779, d170748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49672 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123792 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123793 q = 1) (hb : d170749 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123793, d170749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123793, d170749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d123806 q = 1) (hb : d170762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123806, d170762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49674 q ha hb
    | true =>
      simp only [d123806, d170762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123807 q = 1) (hb : d170763 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123807, d170763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123807, d170763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123808 q = 1) (hb : d170764 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123808, d170764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123808, d170764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123809 q = 1) (hb : d170765 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123809, d170765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123809, d170765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123810 q = 1) (hb : d170766 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123810, d170766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123810, d170766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123811 q = 1) (hb : d170767 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123811, d170767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123811, d170767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro49676 (p : Pattern) (ha : d123791 p = 1) (hb : d170772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123773 q = 1) (hb : d170742 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123773, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49671 q ha hb
    | true =>
      simp only [d123773, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123774 q = 1) (hb : d170743 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123774, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123774, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123788 q = 1) (hb : d170769 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123788, d170769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123788, d170769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123789 q = 1) (hb : d170770 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123789, d170770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123789, d170770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123790 q = 1) (hb : d170771 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123790, d170771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123790, d170771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123791 q = 1) (hb : d170772 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123791, d170772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123791, d170772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49677 (p : Pattern) (ha : d123818 p = 1) (hb : d170778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123813 q = 1) (hb : d170773 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123813, d170773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49676 q ha hb
    | true =>
      simp only [d123813, d170773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123814 q = 1) (hb : d170774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123814, d170774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123814, d170774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123815 q = 1) (hb : d170775 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123815, d170775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123815, d170775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123816 q = 1) (hb : d170776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123816, d170776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123816, d170776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123817 q = 1) (hb : d170777 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123817, d170777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123817, d170777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123818 q = 1) (hb : d170778 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123818, d170778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123818, d170778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49678 (p : Pattern) (ha : d123824 p = 1) (hb : d170784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123589 q = 1) (hb : d170575 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123589, d170575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123589, d170575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49637 q ha hb
  have h2 (q : Pattern) (ha : d123590 q = 1) (hb : d170576 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123590, d170576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123590, d170576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123599 q = 1) (hb : d170585 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123599, d170585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49637 q ha hb
    | true =>
      simp only [d123599, d170585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49640 q ha hb
  have h4 (q : Pattern) (ha : d123600 q = 1) (hb : d170586 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123600, d170586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123600, d170586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123601 q = 1) (hb : d170587 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123601, d170587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123601, d170587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123688 q = 1) (hb : d170672 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123688, d170672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49652 q ha hb
    | true =>
      simp only [d123688, d170672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49660 q ha hb
  have h7 (q : Pattern) (ha : d123706 q = 1) (hb : d170690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123706, d170690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49661 q ha hb
    | true =>
      simp only [d123706, d170690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49662 q ha hb
  have h8 (q : Pattern) (ha : d123707 q = 1) (hb : d170691 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123707, d170691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123707, d170691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123708 q = 1) (hb : d170692 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123708, d170692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123708, d170692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123709 q = 1) (hb : d170693 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123709, d170693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123709, d170693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123713 q = 1) (hb : d170697 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123713, d170697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123713, d170697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49663 q ha hb
  have h12 (q : Pattern) (ha : d123715 q = 1) (hb : d170699 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123715, d170699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123715, d170699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49664 q ha hb
  have h13 (q : Pattern) (ha : d123716 q = 1) (hb : d170700 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123716, d170700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123716, d170700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123717 q = 1) (hb : d170701 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123717, d170701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123717, d170701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d123718 q = 1) (hb : d170702 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123718, d170702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d123718, d170702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d123719 q = 1) (hb : d170703 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123719, d170703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123719, d170703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d123812 q = 1) (hb : d170768 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123812, d170768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123812, d170768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49675 q ha hb
  have h18 (q : Pattern) (ha : d123819 q = 1) (hb : d170779 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123819, d170779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123819, d170779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49677 q ha hb
  have h19 (q : Pattern) (ha : d123820 q = 1) (hb : d170780 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123820, d170780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123820, d170780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d123821 q = 1) (hb : d170781 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123821, d170781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d123821, d170781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d123822 q = 1) (hb : d170782 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123822, d170782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d123822, d170782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d123823 q = 1) (hb : d170783 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123823, d170783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d123823, d170783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d123824 q = 1) (hb : d170784 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d123824, d170784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d123824, d170784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro49679 (p : Pattern) (ha : d123830 p = 1) (hb : d170790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123825 q = 1) (hb : d170785 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d123825, d170785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123825, d170785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49678 q ha hb
  have h2 (q : Pattern) (ha : d123826 q = 1) (hb : d170786 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d123826, d170786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123826, d170786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123827 q = 1) (hb : d170787 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d123827, d170787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123827, d170787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123828 q = 1) (hb : d170788 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d123828, d170788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123828, d170788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123829 q = 1) (hb : d170789 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d123829, d170789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123829, d170789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123830 q = 1) (hb : d170790 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d123830, d170790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123830, d170790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49680 (p : Pattern) (ha : d123836 p = 1) (hb : d170796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d122703 q = 1) (hb : d169789 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d122703, d169789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49442 q ha hb
    | true =>
      simp only [d122703, d169789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49484 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122926 q = 1) (hb : d170005 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d122926, d170005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122926, d170005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49528 q ha hb
  have h3 (q : Pattern) (ha : d122927 q = 1) (hb : d170006 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d122927, d170006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d122927, d170006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123232 q = 1) (hb : d170270 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d123232, d170270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123232, d170270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49579 q ha hb
  have h5 (q : Pattern) (ha : d123233 q = 1) (hb : d170271 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d123233, d170271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123233, d170271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123234 q = 1) (hb : d170272 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d123234, d170272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123234, d170272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123539 q = 1) (hb : d170534 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d123539, d170534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123539, d170534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49630 q ha hb
  have h8 (q : Pattern) (ha : d123540 q = 1) (hb : d170535 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d123540, d170535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123540, d170535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123541 q = 1) (hb : d170536 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d123541, d170536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123541, d170536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123542 q = 1) (hb : d170537 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d123542, d170537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123542, d170537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123831 q = 1) (hb : d170791 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d123831, d170791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123831, d170791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49679 q ha hb
  have h12 (q : Pattern) (ha : d123832 q = 1) (hb : d170792 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d123832, d170792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123832, d170792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123833 q = 1) (hb : d170793 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d123833, d170793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123833, d170793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123834 q = 1) (hb : d170794 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d123834, d170794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123834, d170794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123835 q = 1) (hb : d170795 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d123835, d170795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123835, d170795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123836 q = 1) (hb : d170796 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d123836, d170796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123836, d170796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro49681 (p : Pattern) (ha : d123842 p = 1) (hb : d170802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123837 q = 1) (hb : d170797 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d123837, d170797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49680 q ha hb
    | true =>
      simp only [d123837, d170797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123838 q = 1) (hb : d170798 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d123838, d170798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123838, d170798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123839 q = 1) (hb : d170799 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d123839, d170799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123839, d170799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123840 q = 1) (hb : d170800 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d123840, d170800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123840, d170800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123841 q = 1) (hb : d170801 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d123841, d170801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123841, d170801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123842 q = 1) (hb : d170802 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d123842, d170802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123842, d170802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49682 (p : Pattern) (ha : d123848 p = 1) (hb : d170808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123843 q = 1) (hb : d170803 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d123843, d170803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49681 q ha hb
    | true =>
      simp only [d123843, d170803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123844 q = 1) (hb : d170804 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d123844, d170804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123844, d170804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123845 q = 1) (hb : d170805 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d123845, d170805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123845, d170805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123846 q = 1) (hb : d170806 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d123846, d170806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123846, d170806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123847 q = 1) (hb : d170807 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d123847, d170807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123847, d170807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123848 q = 1) (hb : d170808 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d123848, d170808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123848, d170808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49683 (p : Pattern) (ha : d123854 p = 1) (hb : d170814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123849 q = 1) (hb : d170809 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d123849, d170809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49682 q ha hb
    | true =>
      simp only [d123849, d170809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123850 q = 1) (hb : d170810 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d123850, d170810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123850, d170810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123851 q = 1) (hb : d170811 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d123851, d170811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123851, d170811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123852 q = 1) (hb : d170812 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d123852, d170812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123852, d170812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123853 q = 1) (hb : d170813 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d123853, d170813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123853, d170813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123854 q = 1) (hb : d170814 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d123854, d170814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123854, d170814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49684 (p : Pattern) (ha : d123860 p = 1) (hb : d170820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123855 q = 1) (hb : d170815 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d123855, d170815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49683 q ha hb
    | true =>
      simp only [d123855, d170815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123856 q = 1) (hb : d170816 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d123856, d170816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123856, d170816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123857 q = 1) (hb : d170817 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d123857, d170817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123857, d170817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123858 q = 1) (hb : d170818 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d123858, d170818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123858, d170818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123859 q = 1) (hb : d170819 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d123859, d170819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123859, d170819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123860 q = 1) (hb : d170820 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d123860, d170820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123860, d170820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49685 (p : Pattern) (ha : d123866 p = 1) (hb : d170826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123861 q = 1) (hb : d170821 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d123861, d170821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49684 q ha hb
    | true =>
      simp only [d123861, d170821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123862 q = 1) (hb : d170822 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d123862, d170822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123862, d170822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123863 q = 1) (hb : d170823 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d123863, d170823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123863, d170823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123864 q = 1) (hb : d170824 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d123864, d170824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123864, d170824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123865 q = 1) (hb : d170825 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d123865, d170825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123865, d170825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123866 q = 1) (hb : d170826 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d123866, d170826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123866, d170826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49686 (p : Pattern) (ha : d123872 p = 1) (hb : d170832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123867 q = 1) (hb : d170827 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d123867, d170827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49685 q ha hb
    | true =>
      simp only [d123867, d170827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123868 q = 1) (hb : d170828 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d123868, d170828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123868, d170828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123869 q = 1) (hb : d170829 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d123869, d170829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123869, d170829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123870 q = 1) (hb : d170830 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d123870, d170830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123870, d170830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123871 q = 1) (hb : d170831 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d123871, d170831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123871, d170831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123872 q = 1) (hb : d170832 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d123872, d170832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123872, d170832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49687 (p : Pattern) (ha : d123878 p = 1) (hb : d170838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123873 q = 1) (hb : d170833 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d123873, d170833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49686 q ha hb
    | true =>
      simp only [d123873, d170833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123874 q = 1) (hb : d170834 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d123874, d170834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123874, d170834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123875 q = 1) (hb : d170835 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d123875, d170835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123875, d170835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123876 q = 1) (hb : d170836 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d123876, d170836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123876, d170836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123877 q = 1) (hb : d170837 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d123877, d170837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123877, d170837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123878 q = 1) (hb : d170838 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d123878, d170838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123878, d170838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49688 (p : Pattern) (ha : d169395 p = 1) (hb : d194340 p = 1) : d170841 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d169395 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20913 q = 1) (hb : d169395 q = 1) : d169418 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49128 q ha hb
    | true =>
      simp only [d20913, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20969 q = 1) (hb : d169395 q = 1) : d169473 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20969, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20969, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20970 q = 1) (hb : d169395 q = 1) : d169474 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20970, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20970, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20971 q = 1) (hb : d169395 q = 1) : d169475 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20971, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20971, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20972 q = 1) (hb : d169395 q = 1) : d169476 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20972, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20972, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d169395 q = 1) (hb : d194340 q = 1) : d170841 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194340, d170841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194340, d170841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro49689 (p : Pattern) (ha : d169395 p = 1) (hb : d194350 p = 1) : d170851 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d169395 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20945 q = 1) (hb : d169395 q = 1) : d169449 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20945, d169449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49133 q ha hb
    | true =>
      simp only [d20945, d169449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194346 q = 1) : d170847 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194346, d170847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194346, d170847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194347 q = 1) : d170848 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194347, d170848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194347, d170848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194348 q = 1) : d170849 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194348, d170849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194348, d170849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194349 q = 1) : d170850 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194349, d170850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194349, d170850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d169395 q = 1) (hb : d194350 q = 1) : d170851 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194350, d170851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194350, d170851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro49690 (p : Pattern) (ha : d169395 p = 1) (hb : d194356 p = 1) : d170857 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20974 q = 1) (hb : d169395 q = 1) : d169478 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20974, d169478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49136 q ha hb
    | true =>
      simp only [d20974, d169478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49137 q ha hb
  have h2 (q : Pattern) (ha : d20975 q = 1) (hb : d169395 q = 1) : d169479 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20975, d169479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20975, d169479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194338 q = 1) : d170839 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194338, d170839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194338, d170839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194339 q = 1) : d170840 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194339, d170840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194339, d170840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194341 q = 1) : d170842 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194341, d170842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194341, d170842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49688 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194342 q = 1) : d170843 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194342, d170843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194342, d170843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d169395 q = 1) (hb : d194343 q = 1) : d170844 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194343, d170844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194343, d170844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d169395 q = 1) (hb : d194344 q = 1) : d170845 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194344, d170845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194344, d170845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d169395 q = 1) (hb : d194345 q = 1) : d170846 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194345, d170846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194345, d170846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d169395 q = 1) (hb : d194351 q = 1) : d170852 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194351, d170852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194351, d170852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49689 q ha hb
  have h11 (q : Pattern) (ha : d169395 q = 1) (hb : d194352 q = 1) : d170853 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194352, d170853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194352, d170853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d169395 q = 1) (hb : d194353 q = 1) : d170854 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194353, d170854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194353, d170854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d169395 q = 1) (hb : d194354 q = 1) : d170855 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194354, d170855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194354, d170855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d169395 q = 1) (hb : d194355 q = 1) : d170856 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194355, d170856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194355, d170856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d169395 q = 1) (hb : d194356 q = 1) : d170857 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194356, d170857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194356, d170857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49691 (p : Pattern) (ha : d169395 p = 1) (hb : d194362 p = 1) : d170863 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d169395 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d169395 q = 1) (hb : d194357 q = 1) : d170858 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194357, d170858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194357, d170858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49690 q ha hb
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194358 q = 1) : d170859 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194358, d170859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194358, d170859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194359 q = 1) : d170860 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194359, d170860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194359, d170860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194360 q = 1) : d170861 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194360, d170861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194360, d170861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194361 q = 1) : d170862 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194361, d170862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194361, d170862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d169395 q = 1) (hb : d194362 q = 1) : d170863 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194362, d170863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194362, d170863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro49692 (p : Pattern) (ha : d169395 p = 1) (hb : d194365 p = 1) : d170866 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21156 q = 1) (hb : d169395 q = 1) : d169617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21156, d169617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49164 q ha hb
    | true =>
      simp only [d21156, d169617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49165 q ha hb
  have h2 (q : Pattern) (ha : d21157 q = 1) (hb : d169395 q = 1) : d169618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21157, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21157, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21158 q = 1) (hb : d169395 q = 1) : d169619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21158, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21158, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21159 q = 1) (hb : d169395 q = 1) : d169620 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21159, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21159, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21160 q = 1) (hb : d169395 q = 1) : d169621 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21160, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21160, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194365 q = 1) : d170866 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194365, d170866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194365, d170866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro49693 (p : Pattern) (ha : d169395 p = 1) (hb : d194376 p = 1) : d170877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169395 q = 1) (hb : d194371 q = 1) : d170872 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194371, d170872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49196 q hb ha
    | true =>
      simp only [d194371, d170872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49171 q hb ha
  have h2 (q : Pattern) (ha : d169395 q = 1) (hb : d194372 q = 1) : d170873 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194372, d170873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194372, d170873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194373 q = 1) : d170874 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194373, d170874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194373, d170874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194374 q = 1) : d170875 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194374, d170875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194374, d170875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194375 q = 1) : d170876 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194375, d170876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194375, d170876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194376 q = 1) : d170877 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194376, d170877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194376, d170877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49694 (p : Pattern) (ha : d169395 p = 1) (hb : d194382 p = 1) : d170883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21162 q = 1) (hb : d169395 q = 1) : d169623 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21162, d169623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49163 q ha hb
    | true =>
      simp only [d21162, d169623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49166 q ha hb
  have h2 (q : Pattern) (ha : d21163 q = 1) (hb : d169395 q = 1) : d169624 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21163, d169624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21163, d169624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194363 q = 1) : d170864 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194363, d170864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194363, d170864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194364 q = 1) : d170865 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194364, d170865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194364, d170865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194366 q = 1) : d170867 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194366, d170867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194366, d170867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49692 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194367 q = 1) : d170868 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194367, d170868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194367, d170868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d169395 q = 1) (hb : d194368 q = 1) : d170869 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194368, d170869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194368, d170869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d169395 q = 1) (hb : d194369 q = 1) : d170870 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194369, d170870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194369, d170870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d169395 q = 1) (hb : d194370 q = 1) : d170871 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194370, d170871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194370, d170871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d169395 q = 1) (hb : d194377 q = 1) : d170878 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194377, d170878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194377, d170878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49693 q ha hb
  have h11 (q : Pattern) (ha : d169395 q = 1) (hb : d194378 q = 1) : d170879 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194378, d170879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194378, d170879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d169395 q = 1) (hb : d194379 q = 1) : d170880 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194379, d170880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194379, d170880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d169395 q = 1) (hb : d194380 q = 1) : d170881 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194380, d170881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194380, d170881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d169395 q = 1) (hb : d194381 q = 1) : d170882 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194381, d170882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194381, d170882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d169395 q = 1) (hb : d194382 q = 1) : d170883 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194382, d170883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194382, d170883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49695 (p : Pattern) (ha : d169395 p = 1) (hb : d194388 p = 1) : d170889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169395 q = 1) (hb : d194383 q = 1) : d170884 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194383, d170884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194383, d170884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49694 q ha hb
  have h2 (q : Pattern) (ha : d169395 q = 1) (hb : d194384 q = 1) : d170885 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194384, d170885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194384, d170885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194385 q = 1) : d170886 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194385, d170886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194385, d170886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194386 q = 1) : d170887 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194386, d170887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194386, d170887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194387 q = 1) : d170888 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194387, d170888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194387, d170888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194388 q = 1) : d170889 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194388, d170889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194388, d170889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49696 (p : Pattern) (ha : d169395 p = 1) (hb : d194392 p = 1) : d170893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21455 q = 1) (hb : d169395 q = 1) : d169825 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21455, d169825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49208 q ha hb
    | true =>
      simp only [d21455, d169825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49209 q ha hb
  have h2 (q : Pattern) (ha : d21456 q = 1) (hb : d169395 q = 1) : d169826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21456, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21456, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21457 q = 1) (hb : d169395 q = 1) : d169827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21457, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21457, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21458 q = 1) (hb : d169395 q = 1) : d169828 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21458, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21458, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21459 q = 1) (hb : d169395 q = 1) : d169829 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21459, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21459, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194392 q = 1) : d170893 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194392, d170893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194392, d170893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro49697 (p : Pattern) (ha : d169395 p = 1) (hb : d194403 p = 1) : d170904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169395 q = 1) (hb : d194398 q = 1) : d170899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194398, d170899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49242 q hb ha
    | true =>
      simp only [d194398, d170899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49216 q hb ha
  have h2 (q : Pattern) (ha : d169395 q = 1) (hb : d194399 q = 1) : d170900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194399, d170900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194399, d170900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194400 q = 1) : d170901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194400, d170901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194400, d170901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194401 q = 1) : d170902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194401, d170902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194401, d170902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194402 q = 1) : d170903 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194402, d170903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194402, d170903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194403 q = 1) : d170904 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194403, d170904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194403, d170904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49698 (p : Pattern) (ha : d169395 p = 1) (hb : d194409 p = 1) : d170910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21461 q = 1) (hb : d169395 q = 1) : d169831 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21461, d169831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49207 q ha hb
    | true =>
      simp only [d21461, d169831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49210 q ha hb
  have h2 (q : Pattern) (ha : d21462 q = 1) (hb : d169395 q = 1) : d169832 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21462, d169832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21462, d169832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194390 q = 1) : d170891 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194390, d170891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194390, d170891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194391 q = 1) : d170892 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194391, d170892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194391, d170892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194393 q = 1) : d170894 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194393, d170894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194393, d170894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49696 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194394 q = 1) : d170895 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194394, d170895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194394, d170895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d169395 q = 1) (hb : d194395 q = 1) : d170896 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194395, d170896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194395, d170896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d169395 q = 1) (hb : d194396 q = 1) : d170897 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194396, d170897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194396, d170897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d169395 q = 1) (hb : d194397 q = 1) : d170898 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194397, d170898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194397, d170898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d169395 q = 1) (hb : d194404 q = 1) : d170905 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194404, d170905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194404, d170905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49697 q ha hb
  have h11 (q : Pattern) (ha : d169395 q = 1) (hb : d194405 q = 1) : d170906 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194405, d170906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194405, d170906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d169395 q = 1) (hb : d194406 q = 1) : d170907 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194406, d170907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194406, d170907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d169395 q = 1) (hb : d194407 q = 1) : d170908 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194407, d170908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194407, d170908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d169395 q = 1) (hb : d194408 q = 1) : d170909 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194408, d170909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194408, d170909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d169395 q = 1) (hb : d194409 q = 1) : d170910 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194409, d170910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194409, d170910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49699 (p : Pattern) (ha : d169395 p = 1) (hb : d194415 p = 1) : d170916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169395 q = 1) (hb : d194410 q = 1) : d170911 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194410, d170911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194410, d170911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49698 q ha hb
  have h2 (q : Pattern) (ha : d169395 q = 1) (hb : d194411 q = 1) : d170912 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194411, d170912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194411, d170912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194412 q = 1) : d170913 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194412, d170913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194412, d170913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194413 q = 1) : d170914 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194413, d170914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194413, d170914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194414 q = 1) : d170915 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194414, d170915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194414, d170915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194415 q = 1) : d170916 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194415, d170916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194415, d170916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49700 (p : Pattern) (ha : d169395 p = 1) (hb : d194420 p = 1) : d170921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21808 q = 1) (hb : d169395 q = 1) : d170049 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21808, d170049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49254 q ha hb
    | true =>
      simp only [d21808, d170049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49255 q ha hb
  have h2 (q : Pattern) (ha : d21809 q = 1) (hb : d169395 q = 1) : d170050 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21809, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21809, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21810 q = 1) (hb : d169395 q = 1) : d170051 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21810, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21810, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21811 q = 1) (hb : d169395 q = 1) : d170052 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21811, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21811, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21812 q = 1) (hb : d169395 q = 1) : d170053 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21812, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21812, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194420 q = 1) : d170921 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194420, d170921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194420, d170921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro49701 (p : Pattern) (ha : d169395 p = 1) (hb : d194427 p = 1) : d170928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22070 q = 1) (hb : d169395 q = 1) : d170195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49287 q ha hb
    | true =>
      simp only [d22070, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49262 q ha hb
  have h2 (q : Pattern) (ha : d22071 q = 1) (hb : d169395 q = 1) : d170196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22072 q = 1) (hb : d169395 q = 1) : d170197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22078 q = 1) (hb : d169395 q = 1) : d22078 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22079 q = 1) (hb : d169395 q = 1) : d170198 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22079, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49262 q ha hb
    | true =>
      simp only [d22079, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22080 q = 1) (hb : d169395 q = 1) : d170199 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22080, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22080, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22081 q = 1) (hb : d169395 q = 1) : d170200 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22081, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22081, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22082 q = 1) (hb : d169395 q = 1) : d170201 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22082, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22097 q = 1) (hb : d169395 q = 1) : d22097 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22098 q = 1) (hb : d169395 q = 1) : d170215 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22098, d170215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49262 q ha hb
    | true =>
      simp only [d22098, d170215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22099 q = 1) (hb : d169395 q = 1) : d170216 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22099, d170216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22099, d170216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22100 q = 1) (hb : d169395 q = 1) : d170217 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22100, d170217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22100, d170217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22101 q = 1) (hb : d169395 q = 1) : d170218 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22101, d170218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22101, d170218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d169395 q = 1) (hb : d194426 q = 1) : d170927 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194426, d170927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d194426, d170927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d169395 q = 1) (hb : d194427 q = 1) : d170928 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194427, d170928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d194427, d170928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro49702 (p : Pattern) (ha : d169395 p = 1) (hb : d194433 p = 1) : d170934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169395 q = 1) (hb : d194428 q = 1) : d170929 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194428, d170929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49701 q ha hb
    | true =>
      simp only [d194428, d170929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d169395 q = 1) (hb : d194429 q = 1) : d170930 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194429, d170930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194429, d170930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22104 q = 1) (hb : d169395 q = 1) : d170221 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22104, d170221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49263 q ha hb
    | true =>
      simp only [d22104, d170221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22105 q = 1) (hb : d169395 q = 1) : d170222 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22105, d170222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22105, d170222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194430 q = 1) : d170931 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194430, d170931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194430, d170931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194431 q = 1) : d170932 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194431, d170932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194431, d170932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d169395 q = 1) (hb : d194432 q = 1) : d170933 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194432, d170933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194432, d170933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d169395 q = 1) (hb : d194433 q = 1) : d170934 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194433, d170934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194433, d170934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49703 (p : Pattern) (ha : d169395 p = 1) (hb : d194439 p = 1) : d170940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169395 q = 1) (hb : d194434 q = 1) : d170935 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194434, d170935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49702 q ha hb
    | true =>
      simp only [d194434, d170935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49264 q hb ha
  have h2 (q : Pattern) (ha : d169395 q = 1) (hb : d194435 q = 1) : d170936 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194435, d170936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194435, d170936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194436 q = 1) : d170937 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194436, d170937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194436, d170937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194437 q = 1) : d170938 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194437, d170938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194437, d170938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194438 q = 1) : d170939 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194438, d170939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194438, d170939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194439 q = 1) : d170940 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194439, d170940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194439, d170940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49704 (p : Pattern) (ha : d169395 p = 1) (hb : d194445 p = 1) : d170946 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21814 q = 1) (hb : d169395 q = 1) : d170055 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21814, d170055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49253 q ha hb
    | true =>
      simp only [d21814, d170055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49256 q ha hb
  have h2 (q : Pattern) (ha : d21815 q = 1) (hb : d169395 q = 1) : d170056 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21815, d170056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21815, d170056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194418 q = 1) : d170919 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194418, d170919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194418, d170919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194419 q = 1) : d170920 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194419, d170920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194419, d170920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194421 q = 1) : d170922 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194421, d170922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194421, d170922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49700 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194422 q = 1) : d170923 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194422, d170923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194422, d170923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d169395 q = 1) (hb : d194423 q = 1) : d170924 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194423, d170924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194423, d170924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d169395 q = 1) (hb : d194424 q = 1) : d170925 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194424, d170925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194424, d170925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d169395 q = 1) (hb : d194425 q = 1) : d170926 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194425, d170926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194425, d170926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d169395 q = 1) (hb : d194440 q = 1) : d170941 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194440, d170941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194440, d170941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49703 q ha hb
  have h11 (q : Pattern) (ha : d169395 q = 1) (hb : d194441 q = 1) : d170942 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194441, d170942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194441, d170942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d169395 q = 1) (hb : d194442 q = 1) : d170943 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194442, d170943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194442, d170943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d169395 q = 1) (hb : d194443 q = 1) : d170944 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194443, d170944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194443, d170944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d169395 q = 1) (hb : d194444 q = 1) : d170945 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194444, d170945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194444, d170945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d169395 q = 1) (hb : d194445 q = 1) : d170946 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194445, d170946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194445, d170946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49705 (p : Pattern) (ha : d169395 p = 1) (hb : d194451 p = 1) : d170952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169395 q = 1) (hb : d194446 q = 1) : d170947 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194446, d170947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194446, d170947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49704 q ha hb
  have h2 (q : Pattern) (ha : d169395 q = 1) (hb : d194447 q = 1) : d170948 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194447, d170948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194447, d170948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194448 q = 1) : d170949 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194448, d170949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194448, d170949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194449 q = 1) : d170950 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194449, d170950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194449, d170950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194450 q = 1) : d170951 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194450, d170951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194450, d170951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194451 q = 1) : d170952 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194451, d170952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194451, d170952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49706 (p : Pattern) (ha : d169395 p = 1) (hb : d194457 p = 1) : d170958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22286 q = 1) (hb : d169395 q = 1) : d170315 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22286, d170315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49305 q ha hb
    | true =>
      simp only [d22286, d170315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49306 q ha hb
  have h2 (q : Pattern) (ha : d22287 q = 1) (hb : d169395 q = 1) : d170316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22287, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22287, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22288 q = 1) (hb : d169395 q = 1) : d170317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22288, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22288, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22289 q = 1) (hb : d169395 q = 1) : d170318 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22289, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22289, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22290 q = 1) (hb : d169395 q = 1) : d170319 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22290, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22290, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194457 q = 1) : d170958 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194457, d170958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194457, d170958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro49707 (p : Pattern) (ha : d169395 p = 1) (hb : d194464 p = 1) : d170965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22535 q = 1) (hb : d169395 q = 1) : d170459 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22535, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49338 q ha hb
    | true =>
      simp only [d22535, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49313 q ha hb
  have h2 (q : Pattern) (ha : d22536 q = 1) (hb : d169395 q = 1) : d170460 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22536, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22536, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22537 q = 1) (hb : d169395 q = 1) : d170461 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22537, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22537, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22543 q = 1) (hb : d169395 q = 1) : d22543 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22544 q = 1) (hb : d169395 q = 1) : d170462 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22544, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49313 q ha hb
    | true =>
      simp only [d22544, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22545 q = 1) (hb : d169395 q = 1) : d170463 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22545, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22545, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22546 q = 1) (hb : d169395 q = 1) : d170464 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22546, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22546, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22547 q = 1) (hb : d169395 q = 1) : d170465 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22547, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22547, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22562 q = 1) (hb : d169395 q = 1) : d22562 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22563 q = 1) (hb : d169395 q = 1) : d170479 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22563, d170479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49313 q ha hb
    | true =>
      simp only [d22563, d170479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22564 q = 1) (hb : d169395 q = 1) : d170480 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22564, d170480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22564, d170480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22565 q = 1) (hb : d169395 q = 1) : d170481 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22565, d170481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22565, d170481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22566 q = 1) (hb : d169395 q = 1) : d170482 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22566, d170482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22566, d170482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d169395 q = 1) (hb : d194463 q = 1) : d170964 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194463, d170964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d194463, d170964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d169395 q = 1) (hb : d194464 q = 1) : d170965 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194464, d170965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d194464, d170965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro49708 (p : Pattern) (ha : d169395 p = 1) (hb : d194470 p = 1) : d170971 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169395 q = 1) (hb : d194465 q = 1) : d170966 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194465, d170966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49707 q ha hb
    | true =>
      simp only [d194465, d170966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d169395 q = 1) (hb : d194466 q = 1) : d170967 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194466, d170967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194466, d170967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22569 q = 1) (hb : d169395 q = 1) : d170485 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22569, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49314 q ha hb
    | true =>
      simp only [d22569, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22570 q = 1) (hb : d169395 q = 1) : d170486 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22570, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22570, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194467 q = 1) : d170968 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194467, d170968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194467, d170968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194468 q = 1) : d170969 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194468, d170969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194468, d170969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d169395 q = 1) (hb : d194469 q = 1) : d170970 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194469, d170970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194469, d170970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d169395 q = 1) (hb : d194470 q = 1) : d170971 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194470, d170971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194470, d170971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49709 (p : Pattern) (ha : d169395 p = 1) (hb : d194476 p = 1) : d170977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169395 q = 1) (hb : d194471 q = 1) : d170972 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194471, d170972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49708 q ha hb
    | true =>
      simp only [d194471, d170972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49315 q hb ha
  have h2 (q : Pattern) (ha : d169395 q = 1) (hb : d194472 q = 1) : d170973 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194472, d170973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194472, d170973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194473 q = 1) : d170974 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194473, d170974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194473, d170974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194474 q = 1) : d170975 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194474, d170975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194474, d170975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194475 q = 1) : d170976 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194475, d170976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194475, d170976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194476 q = 1) : d170977 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194476, d170977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194476, d170977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49710 (p : Pattern) (ha : d169395 p = 1) (hb : d194482 p = 1) : d170983 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22292 q = 1) (hb : d169395 q = 1) : d170321 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22292, d170321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49304 q ha hb
    | true =>
      simp only [d22292, d170321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49307 q ha hb
  have h2 (q : Pattern) (ha : d22293 q = 1) (hb : d169395 q = 1) : d170322 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22293, d170322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22293, d170322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194455 q = 1) : d170956 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194455, d170956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194455, d170956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194456 q = 1) : d170957 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194456, d170957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194456, d170957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194458 q = 1) : d170959 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194458, d170959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194458, d170959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49706 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194459 q = 1) : d170960 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194459, d170960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194459, d170960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d169395 q = 1) (hb : d194460 q = 1) : d170961 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194460, d170961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194460, d170961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d169395 q = 1) (hb : d194461 q = 1) : d170962 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194461, d170962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194461, d170962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d169395 q = 1) (hb : d194462 q = 1) : d170963 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194462, d170963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194462, d170963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d169395 q = 1) (hb : d194477 q = 1) : d170978 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194477, d170978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194477, d170978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49709 q ha hb
  have h11 (q : Pattern) (ha : d169395 q = 1) (hb : d194478 q = 1) : d170979 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194478, d170979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194478, d170979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d169395 q = 1) (hb : d194479 q = 1) : d170980 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194479, d170980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194479, d170980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d169395 q = 1) (hb : d194480 q = 1) : d170981 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194480, d170981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194480, d170981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d169395 q = 1) (hb : d194481 q = 1) : d170982 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194481, d170982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194481, d170982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d169395 q = 1) (hb : d194482 q = 1) : d170983 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194482, d170983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194482, d170983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49711 (p : Pattern) (ha : d169395 p = 1) (hb : d194488 p = 1) : d170989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169395 q = 1) (hb : d194483 q = 1) : d170984 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194483, d170984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194483, d170984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49710 q ha hb
  have h2 (q : Pattern) (ha : d169395 q = 1) (hb : d194484 q = 1) : d170985 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194484, d170985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194484, d170985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194485 q = 1) : d170986 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194485, d170986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194485, d170986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194486 q = 1) : d170987 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194486, d170987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194486, d170987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194487 q = 1) : d170988 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194487, d170988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194487, d170988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194488 q = 1) : d170989 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194488, d170989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194488, d170989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49712 (p : Pattern) (ha : d169395 p = 1) (hb : d194495 p = 1) : d170996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22741 q = 1) (hb : d169395 q = 1) : d170579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22741, d170579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49356 q ha hb
    | true =>
      simp only [d22741, d170579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49357 q ha hb
  have h2 (q : Pattern) (ha : d22742 q = 1) (hb : d169395 q = 1) : d170580 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22742, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22742, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22743 q = 1) (hb : d169395 q = 1) : d170581 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22743, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22743, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22744 q = 1) (hb : d169395 q = 1) : d170582 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22744, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22744, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22745 q = 1) (hb : d169395 q = 1) : d170583 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22745, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22745, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194495 q = 1) : d170996 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194495, d170996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194495, d170996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro49713 (p : Pattern) (ha : d169395 p = 1) (hb : d194502 p = 1) : d171003 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22949 q = 1) (hb : d169395 q = 1) : d170716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22949, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49389 q ha hb
    | true =>
      simp only [d22949, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49364 q ha hb
  have h2 (q : Pattern) (ha : d22950 q = 1) (hb : d169395 q = 1) : d170717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22950, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22950, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22951 q = 1) (hb : d169395 q = 1) : d170718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22951, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22951, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22957 q = 1) (hb : d169395 q = 1) : d22957 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22958 q = 1) (hb : d169395 q = 1) : d170719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22958, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49364 q ha hb
    | true =>
      simp only [d22958, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22959 q = 1) (hb : d169395 q = 1) : d170720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22959, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22959, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22960 q = 1) (hb : d169395 q = 1) : d170721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22960, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22960, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22961 q = 1) (hb : d169395 q = 1) : d170722 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22961, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22961, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22976 q = 1) (hb : d169395 q = 1) : d22976 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d22977 q = 1) (hb : d169395 q = 1) : d170736 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22977, d170736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49364 q ha hb
    | true =>
      simp only [d22977, d170736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22978 q = 1) (hb : d169395 q = 1) : d170737 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22978, d170737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22978, d170737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22979 q = 1) (hb : d169395 q = 1) : d170738 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22979, d170738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22979, d170738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22980 q = 1) (hb : d169395 q = 1) : d170739 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22980, d170739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22980, d170739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d169395 q = 1) (hb : d194501 q = 1) : d171002 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194501, d171002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d194501, d171002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d169395 q = 1) (hb : d194502 q = 1) : d171003 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194502, d171003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d194502, d171003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro49714 (p : Pattern) (ha : d169395 p = 1) (hb : d194508 p = 1) : d171009 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169395 q = 1) (hb : d194503 q = 1) : d171004 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194503, d171004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49713 q ha hb
    | true =>
      simp only [d194503, d171004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d169395 q = 1) (hb : d194504 q = 1) : d171005 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194504, d171005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194504, d171005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22983 q = 1) (hb : d169395 q = 1) : d170742 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22983, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49365 q ha hb
    | true =>
      simp only [d22983, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22984 q = 1) (hb : d169395 q = 1) : d170743 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22984, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22984, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194505 q = 1) : d171006 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194505, d171006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194505, d171006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194506 q = 1) : d171007 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194506, d171007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194506, d171007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d169395 q = 1) (hb : d194507 q = 1) : d171008 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194507, d171008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194507, d171008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d169395 q = 1) (hb : d194508 q = 1) : d171009 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194508, d171009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194508, d171009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49715 (p : Pattern) (ha : d169395 p = 1) (hb : d194514 p = 1) : d171015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169395 q = 1) (hb : d194509 q = 1) : d171010 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194509, d171010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49714 q ha hb
    | true =>
      simp only [d194509, d171010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49366 q hb ha
  have h2 (q : Pattern) (ha : d169395 q = 1) (hb : d194510 q = 1) : d171011 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194510, d171011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194510, d171011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194511 q = 1) : d171012 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194511, d171012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194511, d171012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194512 q = 1) : d171013 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194512, d171013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194512, d171013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194513 q = 1) : d171014 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194513, d171014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194513, d171014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194514 q = 1) : d171015 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194514, d171015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194514, d171015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49716 (p : Pattern) (ha : d169395 p = 1) (hb : d194520 p = 1) : d171021 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22747 q = 1) (hb : d169395 q = 1) : d170585 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22747, d170585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49355 q ha hb
    | true =>
      simp only [d22747, d170585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49358 q ha hb
  have h2 (q : Pattern) (ha : d22748 q = 1) (hb : d169395 q = 1) : d170586 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22748, d170586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22748, d170586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194493 q = 1) : d170994 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194493, d170994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194493, d170994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194494 q = 1) : d170995 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194494, d170995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194494, d170995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194496 q = 1) : d170997 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194496, d170997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194496, d170997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49712 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194497 q = 1) : d170998 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194497, d170998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194497, d170998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d169395 q = 1) (hb : d194498 q = 1) : d170999 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194498, d170999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194498, d170999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d169395 q = 1) (hb : d194499 q = 1) : d171000 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194499, d171000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194499, d171000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d169395 q = 1) (hb : d194500 q = 1) : d171001 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194500, d171001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194500, d171001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d169395 q = 1) (hb : d194515 q = 1) : d171016 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194515, d171016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194515, d171016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49715 q ha hb
  have h11 (q : Pattern) (ha : d169395 q = 1) (hb : d194516 q = 1) : d171017 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194516, d171017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194516, d171017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d169395 q = 1) (hb : d194517 q = 1) : d171018 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194517, d171018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194517, d171018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d169395 q = 1) (hb : d194518 q = 1) : d171019 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194518, d171019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194518, d171019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d169395 q = 1) (hb : d194519 q = 1) : d171020 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194519, d171020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194519, d171020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d169395 q = 1) (hb : d194520 q = 1) : d171021 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194520, d171021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194520, d171021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49717 (p : Pattern) (ha : d169395 p = 1) (hb : d194526 p = 1) : d171027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169395 q = 1) (hb : d194521 q = 1) : d171022 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194521, d171022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194521, d171022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49716 q ha hb
  have h2 (q : Pattern) (ha : d169395 q = 1) (hb : d194522 q = 1) : d171023 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194522, d171023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194522, d171023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194523 q = 1) : d171024 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194523, d171024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194523, d171024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194524 q = 1) : d171025 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194524, d171025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194524, d171025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194525 q = 1) : d171026 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194525, d171026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194525, d171026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194526 q = 1) : d171027 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194526, d171027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194526, d171027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49718 (p : Pattern) (ha : d169395 p = 1) (hb : d194532 p = 1) : d171033 p = 1 := by
  have h0 (q : Pattern) (ha : d169395 q = 1) (hb : d194389 q = 1) : d170890 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194389, d170890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49691 q ha hb
    | true =>
      simp only [d194389, d170890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49695 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d169395 q = 1) (hb : d194416 q = 1) : d170917 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194416, d170917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194416, d170917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49699 q ha hb
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194417 q = 1) : d170918 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194417, d170918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194417, d170918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194452 q = 1) : d170953 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194452, d170953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194452, d170953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49705 q ha hb
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194453 q = 1) : d170954 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194453, d170954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194453, d170954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194454 q = 1) : d170955 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d194454, d170955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194454, d170955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d169395 q = 1) (hb : d194489 q = 1) : d170990 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194489, d170990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194489, d170990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49711 q ha hb
  have h8 (q : Pattern) (ha : d169395 q = 1) (hb : d194490 q = 1) : d170991 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194490, d170991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194490, d170991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d169395 q = 1) (hb : d194491 q = 1) : d170992 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d194491, d170992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194491, d170992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d169395 q = 1) (hb : d194492 q = 1) : d170993 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d194492, d170993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194492, d170993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d169395 q = 1) (hb : d194527 q = 1) : d171028 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194527, d171028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194527, d171028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49717 q ha hb
  have h12 (q : Pattern) (ha : d169395 q = 1) (hb : d194528 q = 1) : d171029 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194528, d171029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194528, d171029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d169395 q = 1) (hb : d194529 q = 1) : d171030 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d194529, d171030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194529, d171030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d169395 q = 1) (hb : d194530 q = 1) : d171031 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d194530, d171031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194530, d171031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d169395 q = 1) (hb : d194531 q = 1) : d171032 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d194531, d171032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194531, d171032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d169395 q = 1) (hb : d194532 q = 1) : d171033 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d194532, d171033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d194532, d171033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro49719 (p : Pattern) (ha : d169395 p = 1) (hb : d194538 p = 1) : d171039 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169395 q = 1) (hb : d194533 q = 1) : d171034 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d194533, d171034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49718 q ha hb
    | true =>
      simp only [d194533, d171034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d169395 q = 1) (hb : d194534 q = 1) : d171035 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d194534, d171035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194534, d171035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194535 q = 1) : d171036 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d194535, d171036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194535, d171036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194536 q = 1) : d171037 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d194536, d171037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194536, d171037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194537 q = 1) : d171038 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d194537, d171038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194537, d171038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194538 q = 1) : d171039 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d194538, d171039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194538, d171039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49720 (p : Pattern) (ha : d169395 p = 1) (hb : d194544 p = 1) : d171045 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169395 q = 1) (hb : d194539 q = 1) : d171040 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d194539, d171040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49719 q ha hb
    | true =>
      simp only [d194539, d171040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d169395 q = 1) (hb : d194540 q = 1) : d171041 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d194540, d171041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194540, d171041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194541 q = 1) : d171042 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d194541, d171042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194541, d171042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194542 q = 1) : d171043 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d194542, d171043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194542, d171043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194543 q = 1) : d171044 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d194543, d171044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194543, d171044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d169395 q = 1) (hb : d194544 q = 1) : d171045 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d194544, d171045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194544, d171045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49721 (p : Pattern) (ha : d169397 p = 1) (hb : d194550 p = 1) : d171051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169395 q = 1) (hb : d194545 q = 1) : d171046 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d194545, d171046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49720 q ha hb
    | true =>
      simp only [d194545, d171046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d169395 q = 1) (hb : d194546 q = 1) : d171047 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d194546, d171047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194546, d171047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d169395 q = 1) (hb : d194547 q = 1) : d171048 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d194547, d171048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194547, d171048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d169395 q = 1) (hb : d194548 q = 1) : d171049 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d194548, d171049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194548, d171049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d169395 q = 1) (hb : d194549 q = 1) : d171050 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d194549, d171050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194549, d171050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d169396 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d169397 q = 1) (hb : d194550 q = 1) : d171051 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d169397, d194550, d171051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d169397, d194550, d171051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro49722 (p : Pattern) (ha : d169397 p = 1) (hb : d194556 p = 1) : d171057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169397 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169397 q = 1) (hb : d194551 q = 1) : d171052 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d194551, d171052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49721 q ha hb
    | true =>
      simp only [d194551, d171052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d169397 q = 1) (hb : d194552 q = 1) : d171053 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d194552, d171053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194552, d171053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d169397 q = 1) (hb : d194553 q = 1) : d171054 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d194553, d171054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194553, d171054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d169397 q = 1) (hb : d194554 q = 1) : d171055 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d194554, d171055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194554, d171055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d169397 q = 1) (hb : d194555 q = 1) : d171056 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d194555, d171056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194555, d171056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d169397 q = 1) (hb : d194556 q = 1) : d171057 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d194556, d171057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194556, d171057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49723 (p : Pattern) (ha : d169397 p = 1) (hb : d194562 p = 1) : d171063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169397 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169397 q = 1) (hb : d194557 q = 1) : d171058 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d194557, d171058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49722 q ha hb
    | true =>
      simp only [d194557, d171058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d169397 q = 1) (hb : d194558 q = 1) : d171059 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d194558, d171059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194558, d171059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d169397 q = 1) (hb : d194559 q = 1) : d171060 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d194559, d171060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194559, d171060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d169397 q = 1) (hb : d194560 q = 1) : d171061 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d194560, d171061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194560, d171061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d169397 q = 1) (hb : d194561 q = 1) : d171062 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d194561, d171062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194561, d171062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d169397 q = 1) (hb : d194562 q = 1) : d171063 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d194562, d171063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194562, d171063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49724 (p : Pattern) (ha : d169397 p = 1) (hb : d194568 p = 1) : d171069 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169397 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169397 q = 1) (hb : d194563 q = 1) : d171064 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d194563, d171064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49723 q ha hb
    | true =>
      simp only [d194563, d171064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d169397 q = 1) (hb : d194564 q = 1) : d171065 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d194564, d171065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194564, d171065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d169397 q = 1) (hb : d194565 q = 1) : d171066 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d194565, d171066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194565, d171066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d169397 q = 1) (hb : d194566 q = 1) : d171067 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d194566, d171067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194566, d171067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d169397 q = 1) (hb : d194567 q = 1) : d171068 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d194567, d171068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194567, d171068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d169397 q = 1) (hb : d194568 q = 1) : d171069 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d194568, d171069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194568, d171069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49725 (p : Pattern) (ha : d169397 p = 1) (hb : d194574 p = 1) : d171075 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169397 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169397 q = 1) (hb : d194569 q = 1) : d171070 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d194569, d171070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49724 q ha hb
    | true =>
      simp only [d194569, d171070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d169397 q = 1) (hb : d194570 q = 1) : d171071 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d194570, d171071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194570, d171071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d169397 q = 1) (hb : d194571 q = 1) : d171072 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d194571, d171072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194571, d171072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d169397 q = 1) (hb : d194572 q = 1) : d171073 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d194572, d171073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194572, d171073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d169397 q = 1) (hb : d194573 q = 1) : d171074 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d194573, d171074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194573, d171074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d169397 q = 1) (hb : d194574 q = 1) : d171075 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d194574, d171075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194574, d171075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49726 (p : Pattern) (ha : d122430 p = 1) (hb : d169470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122397 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122403 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d122419 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d122321 q = 1) (hb : d169411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122321, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49410 q ha hb
    | true =>
      simp only [d122321, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d122420 q = 1) (hb : d169466 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122420, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d122420, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122426 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d122427 q = 1) (hb : d169467 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122427, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122427, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d122428 q = 1) (hb : d169468 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122428, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d122428, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122429 q = 1) (hb : d169469 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122429, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122429, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122430 q = 1) (hb : d169470 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122430, d169470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122430, d169470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49727 (p : Pattern) (ha : d122449 p = 1) (hb : d169477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122397 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122403 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122419 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122321 q = 1) (hb : d169411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122321, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49410 q ha hb
    | true =>
      simp only [d122321, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d122420 q = 1) (hb : d169466 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122420, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d122420, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d122426 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d122427 q = 1) (hb : d169467 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122427, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122427, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d122428 q = 1) (hb : d169468 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122428, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122428, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122429 q = 1) (hb : d169469 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122429, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122429, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122435 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d122439 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122441 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d122328 q = 1) (hb : d169418 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122328, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49412 q ha hb
    | true =>
      simp only [d122328, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d122442 q = 1) (hb : d169473 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122442, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d122442, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d122445 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d122446 q = 1) (hb : d169474 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122446, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122446, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d122447 q = 1) (hb : d169475 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122447, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d122447, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122448 q = 1) (hb : d169476 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122448, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d122448, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d122449 q = 1) (hb : d169477 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122449, d169477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122449, d169477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49728 (p : Pattern) (ha : d122458 p = 1) (hb : d170841 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122441 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122328 q = 1) (hb : d169418 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122328, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49412 q ha hb
    | true =>
      simp only [d122328, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d122442 q = 1) (hb : d169473 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122442, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122442, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122445 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122446 q = 1) (hb : d169474 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122446, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122446, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122456 q = 1) (hb : d169475 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122456, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122456, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122457 q = 1) (hb : d169476 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122457, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122457, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122458 q = 1) (hb : d170841 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122458, d170841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122458, d170841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49729 (p : Pattern) (ha : d122490 p = 1) (hb : d170851 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122479 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122360 q = 1) (hb : d169449 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122360, d169449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49417 q ha hb
    | true =>
      simp only [d122360, d169449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d122480 q = 1) (hb : d170847 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122480, d170847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122480, d170847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122486 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122487 q = 1) (hb : d170848 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122487, d170848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122487, d170848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122488 q = 1) (hb : d170849 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122488, d170849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122488, d170849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122489 q = 1) (hb : d170850 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122489, d170850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122489, d170850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122490 q = 1) (hb : d170851 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122490, d170851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122490, d170851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49730 (p : Pattern) (ha : d122496 p = 1) (hb : d170857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122391 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122450 q = 1) (hb : d169478 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122450, d169478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49726 q ha hb
    | true =>
      simp only [d122450, d169478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49727 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122452 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122453 q = 1) (hb : d169479 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122453, d169479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122453, d169479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122454 q = 1) (hb : d170839 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122454, d170839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122454, d170839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122455 q = 1) (hb : d170840 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122455, d170840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122455, d170840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122459 q = 1) (hb : d170842 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122459, d170842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122459, d170842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49728 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d122460 q = 1) (hb : d170843 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122460, d170843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122460, d170843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d122461 q = 1) (hb : d170844 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122461, d170844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d122461, d170844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d122462 q = 1) (hb : d170845 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122462, d170845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122462, d170845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d122463 q = 1) (hb : d170846 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122463, d170846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122463, d170846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122491 q = 1) (hb : d170852 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122491, d170852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122491, d170852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49729 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d122492 q = 1) (hb : d170853 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122492, d170853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122492, d170853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d122493 q = 1) (hb : d170854 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122493, d170854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122493, d170854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d122494 q = 1) (hb : d170855 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122494, d170855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d122494, d170855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d122495 q = 1) (hb : d170856 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122495, d170856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122495, d170856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d122496 q = 1) (hb : d170857 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d122496, d170857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d122496, d170857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49731 (p : Pattern) (ha : d122502 p = 1) (hb : d170863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d122372 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d122372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d122372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22453 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d122373 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d122373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d122373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d122374 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d122374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d122374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d122375 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d122375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d122375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d122376 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d122376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d122376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122497 q = 1) (hb : d170858 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d122497, d170858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122497, d170858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49730 q ha hb
  have h8 (q : Pattern) (ha : d122498 q = 1) (hb : d170859 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d122498, d170859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122498, d170859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122499 q = 1) (hb : d170860 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d122499, d170860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122499, d170860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122500 q = 1) (hb : d170861 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d122500, d170861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122500, d170861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122501 q = 1) (hb : d170862 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d122501, d170862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122501, d170862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d122502 q = 1) (hb : d170863 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d122502, d170863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d122502, d170863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro49732 (p : Pattern) (ha : d122586 p = 1) (hb : d169612 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122546 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122555 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d122575 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d122520 q = 1) (hb : d169607 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122520, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49445 q ha hb
    | true =>
      simp only [d122520, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49446 q ha hb
  have h5 (q : Pattern) (ha : d122576 q = 1) (hb : d169608 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122576, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d122576, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122582 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d122583 q = 1) (hb : d169609 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122583, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122583, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d122584 q = 1) (hb : d169610 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122584, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d122584, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122585 q = 1) (hb : d169611 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122585, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122585, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122586 q = 1) (hb : d169612 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122586, d169612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122586, d169612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49733 (p : Pattern) (ha : d122607 p = 1) (hb : d169622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122546 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122555 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122575 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122520 q = 1) (hb : d169607 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122520, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49445 q ha hb
    | true =>
      simp only [d122520, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49446 q ha hb
  have h4 (q : Pattern) (ha : d122576 q = 1) (hb : d169608 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122576, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d122576, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d122582 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d122583 q = 1) (hb : d169609 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122583, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122583, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d122584 q = 1) (hb : d169610 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122584, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122584, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122585 q = 1) (hb : d169611 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122585, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122585, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122592 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d122597 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122599 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d122530 q = 1) (hb : d169617 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122530, d169617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49448 q ha hb
    | true =>
      simp only [d122530, d169617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49449 q ha hb
  have h13 (q : Pattern) (ha : d122600 q = 1) (hb : d169618 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122600, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d122600, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d122603 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d122604 q = 1) (hb : d169619 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122604, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122604, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d122605 q = 1) (hb : d169620 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122605, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d122605, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122606 q = 1) (hb : d169621 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122606, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d122606, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d122607 q = 1) (hb : d169622 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122607, d169622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122607, d169622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49734 (p : Pattern) (ha : d122627 p = 1) (hb : d170866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122599 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122530 q = 1) (hb : d169617 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122530, d169617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49448 q ha hb
    | true =>
      simp only [d122530, d169617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49449 q ha hb
  have h3 (q : Pattern) (ha : d122600 q = 1) (hb : d169618 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122600, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122600, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122603 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122604 q = 1) (hb : d169619 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122604, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122604, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122625 q = 1) (hb : d169620 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122625, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122625, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122626 q = 1) (hb : d169621 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122626, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122626, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122627 q = 1) (hb : d170866 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122627, d170866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122627, d170866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49735 (p : Pattern) (ha : d122683 p = 1) (hb : d170877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122667 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122672 q = 1) (hb : d170872 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122672, d170872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49478 q ha hb
    | true =>
      simp only [d122672, d170872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49481 q ha hb
  have h3 (q : Pattern) (ha : d122673 q = 1) (hb : d170873 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122673, d170873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122673, d170873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122679 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122680 q = 1) (hb : d170874 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122680, d170874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122680, d170874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122681 q = 1) (hb : d170875 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122681, d170875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122681, d170875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122682 q = 1) (hb : d170876 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122682, d170876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122682, d170876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122683 q = 1) (hb : d170877 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122683, d170877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122683, d170877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49736 (p : Pattern) (ha : d122696 p = 1) (hb : d170883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122538 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122608 q = 1) (hb : d169623 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122608, d169623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49732 q ha hb
    | true =>
      simp only [d122608, d169623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49733 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122621 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122622 q = 1) (hb : d169624 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122622, d169624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122622, d169624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122623 q = 1) (hb : d170864 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122623, d170864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122623, d170864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122624 q = 1) (hb : d170865 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122624, d170865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122624, d170865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122628 q = 1) (hb : d170867 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122628, d170867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122628, d170867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49734 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d122630 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d122631 q = 1) (hb : d170868 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122631, d170868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122631, d170868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d122632 q = 1) (hb : d170869 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122632, d170869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d122632, d170869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d122633 q = 1) (hb : d170870 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122633, d170870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122633, d170870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d122634 q = 1) (hb : d170871 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122634, d170871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122634, d170871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122684 q = 1) (hb : d170878 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122684, d170878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122684, d170878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49735 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d122691 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d122692 q = 1) (hb : d170879 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122692, d170879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122692, d170879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d122693 q = 1) (hb : d170880 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122693, d170880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122693, d170880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d122694 q = 1) (hb : d170881 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122694, d170881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d122694, d170881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d122695 q = 1) (hb : d170882 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122695, d170882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122695, d170882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d122696 q = 1) (hb : d170883 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d122696, d170883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d122696, d170883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49737 (p : Pattern) (ha : d122702 p = 1) (hb : d170889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122697 q = 1) (hb : d170884 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d122697, d170884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122697, d170884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49736 q ha hb
  have h2 (q : Pattern) (ha : d122698 q = 1) (hb : d170885 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d122698, d170885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122698, d170885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122699 q = 1) (hb : d170886 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d122699, d170886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122699, d170886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122700 q = 1) (hb : d170887 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d122700, d170887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122700, d170887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122701 q = 1) (hb : d170888 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d122701, d170888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122701, d170888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122702 q = 1) (hb : d170889 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d122702, d170889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122702, d170889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49738 (p : Pattern) (ha : d122797 p = 1) (hb : d169820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122755 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d122786 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d122729 q = 1) (hb : d169815 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122729, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49488 q ha hb
    | true =>
      simp only [d122729, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49489 q ha hb
  have h5 (q : Pattern) (ha : d122787 q = 1) (hb : d169816 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122787, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d122787, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122793 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d122794 q = 1) (hb : d169817 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122794, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d122794, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d122795 q = 1) (hb : d169818 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122795, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d122795, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122796 q = 1) (hb : d169819 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122796, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122796, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122797 q = 1) (hb : d169820 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122797, d169820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122797, d169820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49739 (p : Pattern) (ha : d122818 p = 1) (hb : d169830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122764 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122786 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122729 q = 1) (hb : d169815 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122729, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49488 q ha hb
    | true =>
      simp only [d122729, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49489 q ha hb
  have h4 (q : Pattern) (ha : d122787 q = 1) (hb : d169816 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122787, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d122787, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d122793 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d122794 q = 1) (hb : d169817 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122794, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122794, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d122795 q = 1) (hb : d169818 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122795, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122795, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122796 q = 1) (hb : d169819 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122796, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122796, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122803 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d122808 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122810 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d122739 q = 1) (hb : d169825 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122739, d169825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49491 q ha hb
    | true =>
      simp only [d122739, d169825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49492 q ha hb
  have h13 (q : Pattern) (ha : d122811 q = 1) (hb : d169826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122811, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d122811, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d122814 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d122815 q = 1) (hb : d169827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122815, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122815, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d122816 q = 1) (hb : d169828 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122816, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d122816, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122817 q = 1) (hb : d169829 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122817, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d122817, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d122818 q = 1) (hb : d169830 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122818, d169830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122818, d169830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49740 (p : Pattern) (ha : d122838 p = 1) (hb : d170893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122810 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122739 q = 1) (hb : d169825 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122739, d169825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49491 q ha hb
    | true =>
      simp only [d122739, d169825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49492 q ha hb
  have h3 (q : Pattern) (ha : d122811 q = 1) (hb : d169826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122811, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122811, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122814 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122815 q = 1) (hb : d169827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122815, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122815, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122836 q = 1) (hb : d169828 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122836, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122836, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122837 q = 1) (hb : d169829 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122837, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122837, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122838 q = 1) (hb : d170893 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122838, d170893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122838, d170893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49741 (p : Pattern) (ha : d122906 p = 1) (hb : d170904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122890 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122895 q = 1) (hb : d170899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122895, d170899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49522 q ha hb
    | true =>
      simp only [d122895, d170899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49525 q ha hb
  have h3 (q : Pattern) (ha : d122896 q = 1) (hb : d170900 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122896, d170900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122896, d170900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122902 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122903 q = 1) (hb : d170901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122903, d170901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122903, d170901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122904 q = 1) (hb : d170902 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122904, d170902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122904, d170902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122905 q = 1) (hb : d170903 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122905, d170903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122905, d170903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122906 q = 1) (hb : d170904 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122906, d170904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122906, d170904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49742 (p : Pattern) (ha : d122919 p = 1) (hb : d170910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122819 q = 1) (hb : d169831 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122819, d169831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49738 q ha hb
    | true =>
      simp only [d122819, d169831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49739 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122832 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122833 q = 1) (hb : d169832 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122833, d169832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d122833, d169832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122834 q = 1) (hb : d170891 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122834, d170891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122834, d170891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122835 q = 1) (hb : d170892 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122835, d170892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122835, d170892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122839 q = 1) (hb : d170894 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122839, d170894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122839, d170894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49740 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d122841 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d122842 q = 1) (hb : d170895 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122842, d170895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122842, d170895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d122843 q = 1) (hb : d170896 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122843, d170896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d122843, d170896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d122844 q = 1) (hb : d170897 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122844, d170897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122844, d170897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d122845 q = 1) (hb : d170898 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122845, d170898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122845, d170898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122907 q = 1) (hb : d170905 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122907, d170905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122907, d170905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49741 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d122914 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d122915 q = 1) (hb : d170906 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122915, d170906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122915, d170906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d122916 q = 1) (hb : d170907 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122916, d170907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122916, d170907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d122917 q = 1) (hb : d170908 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122917, d170908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d122917, d170908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d122918 q = 1) (hb : d170909 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122918, d170909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122918, d170909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d122919 q = 1) (hb : d170910 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d122919, d170910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d122919, d170910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49743 (p : Pattern) (ha : d122925 p = 1) (hb : d170916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122920 q = 1) (hb : d170911 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d122920, d170911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122920, d170911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49742 q ha hb
  have h2 (q : Pattern) (ha : d122921 q = 1) (hb : d170912 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d122921, d170912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122921, d170912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122922 q = 1) (hb : d170913 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d122922, d170913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122922, d170913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122923 q = 1) (hb : d170914 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d122923, d170914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122923, d170914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122924 q = 1) (hb : d170915 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d122924, d170915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122924, d170915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122925 q = 1) (hb : d170916 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d122925, d170916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122925, d170916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49744 (p : Pattern) (ha : d123056 p = 1) (hb : d170044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122996 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123005 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d123037 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d122970 q = 1) (hb : d170039 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122970, d170039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49533 q ha hb
    | true =>
      simp only [d122970, d170039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49534 q ha hb
  have h5 (q : Pattern) (ha : d123038 q = 1) (hb : d170040 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123038, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d123038, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123052 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d123053 q = 1) (hb : d170041 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123053, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123053, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d123054 q = 1) (hb : d170042 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123054, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d123054, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123055 q = 1) (hb : d170043 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123055, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123055, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123056 q = 1) (hb : d170044 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123056, d170044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123056, d170044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49745 (p : Pattern) (ha : d123078 p = 1) (hb : d170054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122996 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123005 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123037 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122970 q = 1) (hb : d170039 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122970, d170039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49533 q ha hb
    | true =>
      simp only [d122970, d170039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49534 q ha hb
  have h4 (q : Pattern) (ha : d123038 q = 1) (hb : d170040 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123038, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d123038, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d123052 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d123053 q = 1) (hb : d170041 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123053, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123053, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d123054 q = 1) (hb : d170042 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123054, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123054, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123055 q = 1) (hb : d170043 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123055, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123055, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123062 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d123067 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d123070 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d122980 q = 1) (hb : d170049 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122980, d170049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49536 q ha hb
    | true =>
      simp only [d122980, d170049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49537 q ha hb
  have h13 (q : Pattern) (ha : d123071 q = 1) (hb : d170050 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123071, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d123071, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123074 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123075 q = 1) (hb : d170051 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123075, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123075, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d123076 q = 1) (hb : d170052 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123076, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d123076, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d123077 q = 1) (hb : d170053 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123077, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d123077, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d123078 q = 1) (hb : d170054 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123078, d170054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123078, d170054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49746 (p : Pattern) (ha : d123103 p = 1) (hb : d170921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123070 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122980 q = 1) (hb : d170049 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122980, d170049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49536 q ha hb
    | true =>
      simp only [d122980, d170049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49537 q ha hb
  have h3 (q : Pattern) (ha : d123071 q = 1) (hb : d170050 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123071, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123071, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123074 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123075 q = 1) (hb : d170051 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123075, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123075, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123101 q = 1) (hb : d170052 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123101, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123101, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123102 q = 1) (hb : d170053 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123102, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123102, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123103 q = 1) (hb : d170921 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123103, d170921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123103, d170921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49747 (p : Pattern) (ha : d123182 p = 1) (hb : d170928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123141 q = 1) (hb : d170195 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123141, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49565 q ha hb
    | true =>
      simp only [d123141, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49567 q ha hb
  have h2 (q : Pattern) (ha : d123142 q = 1) (hb : d170196 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123142, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123142, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123143 q = 1) (hb : d170197 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123143, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123143, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123150 q = 1) (hb : d170198 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123150, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49567 q ha hb
    | true =>
      simp only [d123150, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48890 q hb ha
  have h5 (q : Pattern) (ha : d123151 q = 1) (hb : d170199 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123151, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123151, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123152 q = 1) (hb : d170200 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123152, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123152, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123153 q = 1) (hb : d170201 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123153, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123153, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123168 q = 1) (hb : d170215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123168, d170215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49567 q ha hb
    | true =>
      simp only [d123168, d170215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48862 q hb ha
  have h9 (q : Pattern) (ha : d123169 q = 1) (hb : d170216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123169, d170216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123169, d170216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123170 q = 1) (hb : d170217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123170, d170217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123170, d170217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123171 q = 1) (hb : d170218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123171, d170218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123171, d170218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123181 q = 1) (hb : d170927 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123181, d170927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123181, d170927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123182 q = 1) (hb : d170928 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123182, d170928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123182, d170928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro49748 (p : Pattern) (ha : d123188 p = 1) (hb : d170934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123183 q = 1) (hb : d170929 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123183, d170929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49747 q ha hb
    | true =>
      simp only [d123183, d170929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123184 q = 1) (hb : d170930 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123184, d170930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123184, d170930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123174 q = 1) (hb : d170221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123174, d170221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49571 q ha hb
    | true =>
      simp only [d123174, d170221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123175 q = 1) (hb : d170222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123175, d170222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123175, d170222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123185 q = 1) (hb : d170931 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123185, d170931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123185, d170931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123186 q = 1) (hb : d170932 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123186, d170932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123186, d170932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123187 q = 1) (hb : d170933 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123187, d170933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123187, d170933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123188 q = 1) (hb : d170934 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123188, d170934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123188, d170934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49749 (p : Pattern) (ha : d123212 p = 1) (hb : d170940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123180 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d123193 q = 1) (hb : d170935 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123193, d170935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49748 q ha hb
    | true =>
      simp only [d123193, d170935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49576 q ha hb
  have h3 (q : Pattern) (ha : d123194 q = 1) (hb : d170936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123194, d170936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123194, d170936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123208 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123209 q = 1) (hb : d170937 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123209, d170937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123209, d170937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123210 q = 1) (hb : d170938 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123210, d170938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123210, d170938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123211 q = 1) (hb : d170939 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123211, d170939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123211, d170939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123212 q = 1) (hb : d170940 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123212, d170940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123212, d170940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
