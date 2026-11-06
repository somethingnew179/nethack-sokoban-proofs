import NetHack.Soko22Hazard87.AndIntroBlocks0086
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro21750 (p : Pattern) (ha : d75748 p = 1) (hb : d93986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75743 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d75655 q = 1) (hb : d93294 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75655, d93294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18949 q hb ha
    | true =>
      simp only [d75655, d93294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d75744 q = 1) (hb : d93982 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75744, d93982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75744, d93982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75745 q = 1) (hb : d93983 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75745, d93983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75745, d93983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d75746 q = 1) (hb : d93984 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75746, d93984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75746, d93984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75747 q = 1) (hb : d93985 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75747, d93985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75747, d93985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75748 q = 1) (hb : d93986 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75748, d93986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75748, d93986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21751 (p : Pattern) (ha : d75754 p = 1) (hb : d93992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75725 q = 1) (hb : d93323 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75725, d93323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21747 q ha hb
    | true =>
      simp only [d75725, d93323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21748 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75727 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75728 q = 1) (hb : d93324 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75728, d93324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d75728, d93324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75729 q = 1) (hb : d93974 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75729, d93974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75729, d93974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d75730 q = 1) (hb : d93975 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75730, d93975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75730, d93975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75734 q = 1) (hb : d93977 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75734, d93977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75734, d93977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21749 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d75735 q = 1) (hb : d93978 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75735, d93978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75735, d93978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d75736 q = 1) (hb : d93979 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75736, d93979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d75736, d93979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d75737 q = 1) (hb : d93980 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75737, d93980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75737, d93980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d75738 q = 1) (hb : d93981 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75738, d93981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75738, d93981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d75749 q = 1) (hb : d93987 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75749, d93987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75749, d93987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21750 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75750 q = 1) (hb : d93988 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75750, d93988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d75750, d93988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75751 q = 1) (hb : d93989 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75751, d93989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d75751, d93989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d75752 q = 1) (hb : d93990 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75752, d93990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d75752, d93990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d75753 q = 1) (hb : d93991 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75753, d93991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d75753, d93991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d75754 q = 1) (hb : d93992 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d75754, d93992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d75754, d93992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro21752 (p : Pattern) (ha : d75760 p = 1) (hb : d93998 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d75755 q = 1) (hb : d93993 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d75755, d93993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75755, d93993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21751 q ha hb
  have h8 (q : Pattern) (ha : d75756 q = 1) (hb : d93994 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d75756, d93994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75756, d93994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75757 q = 1) (hb : d93995 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d75757, d93995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75757, d93995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75758 q = 1) (hb : d93996 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d75758, d93996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75758, d93996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75759 q = 1) (hb : d93997 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d75759, d93997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75759, d93997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d75760 q = 1) (hb : d93998 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d75760, d93998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d75760, d93998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro21753 (p : Pattern) (ha : d75799 p = 1) (hb : d93396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75783 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75789 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d75794 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d75761 q = 1) (hb : d93391 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75761, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18965 q hb ha
    | true =>
      simp only [d75761, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h5 (q : Pattern) (ha : d75795 q = 1) (hb : d93392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75795, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d75795, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d75796 q = 1) (hb : d93393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75796, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75796, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75797 q = 1) (hb : d93394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75797, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d75797, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75798 q = 1) (hb : d93395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75798, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75798, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75799 q = 1) (hb : d93396 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75799, d93396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75799, d93396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro21754 (p : Pattern) (ha : d75816 p = 1) (hb : d93404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75783 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75789 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75794 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75761 q = 1) (hb : d93391 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75761, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18965 q hb ha
    | true =>
      simp only [d75761, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h4 (q : Pattern) (ha : d75795 q = 1) (hb : d93392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75795, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d75795, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d75796 q = 1) (hb : d93393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75796, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75796, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75797 q = 1) (hb : d93394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75797, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75797, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75798 q = 1) (hb : d93395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75798, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75798, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d75804 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d75808 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d75811 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d75769 q = 1) (hb : d93399 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75769, d93399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18971 q hb ha
    | true =>
      simp only [d75769, d93399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q hb ha
  have h13 (q : Pattern) (ha : d75812 q = 1) (hb : d93400 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75812, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d75812, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75813 q = 1) (hb : d93401 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75813, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d75813, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75814 q = 1) (hb : d93402 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75814, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d75814, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75815 q = 1) (hb : d93403 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75815, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d75815, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d75816 q = 1) (hb : d93404 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75816, d93404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75816, d93404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro21755 (p : Pattern) (ha : d75830 p = 1) (hb : d94001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75811 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d75769 q = 1) (hb : d93399 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75769, d93399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18971 q hb ha
    | true =>
      simp only [d75769, d93399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q hb ha
  have h3 (q : Pattern) (ha : d75812 q = 1) (hb : d93400 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75812, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75812, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75813 q = 1) (hb : d93401 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75813, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75813, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d75828 q = 1) (hb : d93402 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75828, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75828, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75829 q = 1) (hb : d93403 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75829, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75829, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75830 q = 1) (hb : d94001 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75830, d94001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75830, d94001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21756 (p : Pattern) (ha : d75859 p = 1) (hb : d94012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75853 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d75854 q = 1) (hb : d94007 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75854, d94007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18979 q hb ha
    | true =>
      simp only [d75854, d94007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72 q hb ha
  have h3 (q : Pattern) (ha : d75855 q = 1) (hb : d94008 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75855, d94008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75855, d94008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74156 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75856 q = 1) (hb : d94009 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75856, d94009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75856, d94009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d75857 q = 1) (hb : d94010 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75857, d94010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75857, d94010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75858 q = 1) (hb : d94011 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75858, d94011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75858, d94011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75859 q = 1) (hb : d94012 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75859, d94012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75859, d94012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21757 (p : Pattern) (ha : d75865 p = 1) (hb : d94018 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75817 q = 1) (hb : d93405 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75817, d93405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21753 q ha hb
    | true =>
      simp only [d75817, d93405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21754 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75824 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75825 q = 1) (hb : d93406 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75825, d93406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d75825, d93406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75826 q = 1) (hb : d93999 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75826, d93999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75826, d93999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d75827 q = 1) (hb : d94000 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75827, d94000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75827, d94000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75831 q = 1) (hb : d94002 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75831, d94002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75831, d94002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21755 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d75832 q = 1) (hb : d94003 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75832, d94003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75832, d94003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d75833 q = 1) (hb : d94004 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75833, d94004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d75833, d94004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d75834 q = 1) (hb : d94005 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75834, d94005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75834, d94005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d75835 q = 1) (hb : d94006 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75835, d94006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75835, d94006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d75860 q = 1) (hb : d94013 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75860, d94013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75860, d94013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21756 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75861 q = 1) (hb : d94014 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75861, d94014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d75861, d94014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75862 q = 1) (hb : d94015 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75862, d94015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d75862, d94015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d75863 q = 1) (hb : d94016 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75863, d94016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d75863, d94016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d75864 q = 1) (hb : d94017 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75864, d94017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d75864, d94017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d75865 q = 1) (hb : d94018 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d75865, d94018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d75865, d94018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro21758 (p : Pattern) (ha : d75871 p = 1) (hb : d94024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75866 q = 1) (hb : d94019 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d75866, d94019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75866, d94019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21757 q ha hb
  have h2 (q : Pattern) (ha : d75867 q = 1) (hb : d94020 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d75867, d94020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75867, d94020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75868 q = 1) (hb : d94021 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d75868, d94021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75868, d94021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75869 q = 1) (hb : d94022 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d75869, d94022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75869, d94022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75870 q = 1) (hb : d94023 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d75870, d94023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75870, d94023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75871 q = 1) (hb : d94024 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d75871, d94024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75871, d94024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21759 (p : Pattern) (ha : d75918 p = 1) (hb : d93502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75900 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75906 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d75911 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d75877 q = 1) (hb : d93497 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75877, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18995 q hb ha
    | true =>
      simp only [d75877, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h5 (q : Pattern) (ha : d75912 q = 1) (hb : d93498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75912, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d75912, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d75914 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d75915 q = 1) (hb : d93499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75915, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d75915, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75916 q = 1) (hb : d93500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75916, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d75916, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75917 q = 1) (hb : d93501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75917, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75917, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75918 q = 1) (hb : d93502 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75918, d93502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75918, d93502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro21760 (p : Pattern) (ha : d75937 p = 1) (hb : d93510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75900 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75906 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75911 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75877 q = 1) (hb : d93497 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75877, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18995 q hb ha
    | true =>
      simp only [d75877, d93497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h4 (q : Pattern) (ha : d75912 q = 1) (hb : d93498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75912, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d75912, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d75914 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d75915 q = 1) (hb : d93499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75915, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75915, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75916 q = 1) (hb : d93500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75916, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75916, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75917 q = 1) (hb : d93501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75917, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75917, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d75923 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d75927 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d75930 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d75886 q = 1) (hb : d93505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75886, d93505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19001 q hb ha
    | true =>
      simp only [d75886, d93505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q hb ha
  have h13 (q : Pattern) (ha : d75931 q = 1) (hb : d93506 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75931, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d75931, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d75933 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75934 q = 1) (hb : d93507 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75934, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d75934, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75935 q = 1) (hb : d93508 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75935, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d75935, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75936 q = 1) (hb : d93509 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75936, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d75936, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d75937 q = 1) (hb : d93510 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75937, d93510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75937, d93510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro21761 (p : Pattern) (ha : d75951 p = 1) (hb : d94028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75930 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d75886 q = 1) (hb : d93505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75886, d93505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19001 q hb ha
    | true =>
      simp only [d75886, d93505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q hb ha
  have h3 (q : Pattern) (ha : d75931 q = 1) (hb : d93506 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75931, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75931, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d75933 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75934 q = 1) (hb : d93507 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75934, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75934, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d75949 q = 1) (hb : d93508 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75949, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75949, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75950 q = 1) (hb : d93509 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75950, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75950, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75951 q = 1) (hb : d94028 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75951, d94028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75951, d94028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21762 (p : Pattern) (ha : d75986 p = 1) (hb : d94039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d75979 q = 1) (hb : d94034 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d75979, d94034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19009 q hb ha
    | true =>
      simp only [d75979, d94034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro118 q hb ha
  have h3 (q : Pattern) (ha : d75980 q = 1) (hb : d94035 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75980, d94035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75980, d94035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d75982 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75983 q = 1) (hb : d94036 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75983, d94036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75983, d94036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d75984 q = 1) (hb : d94037 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75984, d94037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75984, d94037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75985 q = 1) (hb : d94038 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75985, d94038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75985, d94038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75986 q = 1) (hb : d94039 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75986, d94039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75986, d94039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21763 (p : Pattern) (ha : d75992 p = 1) (hb : d94045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75894 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75938 q = 1) (hb : d93511 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75938, d93511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21759 q ha hb
    | true =>
      simp only [d75938, d93511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21760 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75945 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75946 q = 1) (hb : d93512 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75946, d93512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d75946, d93512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75947 q = 1) (hb : d94026 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75947, d94026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75947, d94026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d75948 q = 1) (hb : d94027 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75948, d94027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75948, d94027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75952 q = 1) (hb : d94029 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75952, d94029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75952, d94029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21761 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d75953 q = 1) (hb : d94030 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75953, d94030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75953, d94030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d75954 q = 1) (hb : d94031 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75954, d94031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d75954, d94031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d75955 q = 1) (hb : d94032 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75955, d94032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75955, d94032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d75956 q = 1) (hb : d94033 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75956, d94033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75956, d94033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d75987 q = 1) (hb : d94040 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75987, d94040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75987, d94040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21762 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75988 q = 1) (hb : d94041 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75988, d94041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d75988, d94041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75989 q = 1) (hb : d94042 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75989, d94042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d75989, d94042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d75990 q = 1) (hb : d94043 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75990, d94043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d75990, d94043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d75991 q = 1) (hb : d94044 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75991, d94044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d75991, d94044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d75992 q = 1) (hb : d94045 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d75992, d94045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d75992, d94045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro21764 (p : Pattern) (ha : d75998 p = 1) (hb : d94051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75993 q = 1) (hb : d94046 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d75993, d94046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75993, d94046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21763 q ha hb
  have h2 (q : Pattern) (ha : d75994 q = 1) (hb : d94047 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d75994, d94047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75994, d94047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75995 q = 1) (hb : d94048 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d75995, d94048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75995, d94048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75996 q = 1) (hb : d94049 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d75996, d94049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75996, d94049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75997 q = 1) (hb : d94050 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d75997, d94050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75997, d94050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75998 q = 1) (hb : d94051 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d75998, d94051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75998, d94051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21765 (p : Pattern) (ha : d76046 p = 1) (hb : d93609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76028 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76034 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d76039 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d76005 q = 1) (hb : d93604 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76005, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19025 q hb ha
    | true =>
      simp only [d76005, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h5 (q : Pattern) (ha : d76040 q = 1) (hb : d93605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76040, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d76040, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d76042 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d76043 q = 1) (hb : d93606 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76043, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76043, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d76044 q = 1) (hb : d93607 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76044, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76044, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76045 q = 1) (hb : d93608 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76045, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76045, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76046 q = 1) (hb : d93609 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76046, d93609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76046, d93609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro21766 (p : Pattern) (ha : d76065 p = 1) (hb : d93617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76028 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76039 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76005 q = 1) (hb : d93604 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76005, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19025 q hb ha
    | true =>
      simp only [d76005, d93604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h4 (q : Pattern) (ha : d76040 q = 1) (hb : d93605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76040, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76040, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76042 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76043 q = 1) (hb : d93606 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76043, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76043, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76044 q = 1) (hb : d93607 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76044, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76044, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76045 q = 1) (hb : d93608 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76045, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76045, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d76051 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d76055 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d76058 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d76014 q = 1) (hb : d93612 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76014, d93612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19031 q hb ha
    | true =>
      simp only [d76014, d93612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q hb ha
  have h13 (q : Pattern) (ha : d76059 q = 1) (hb : d93613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76059, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d76059, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d76061 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76062 q = 1) (hb : d93614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76062, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76062, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76063 q = 1) (hb : d93615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76063, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d76063, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76064 q = 1) (hb : d93616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76064, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d76064, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76065 q = 1) (hb : d93617 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76065, d93617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76065, d93617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro21767 (p : Pattern) (ha : d76079 p = 1) (hb : d94056 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76058 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d76014 q = 1) (hb : d93612 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76014, d93612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19031 q hb ha
    | true =>
      simp only [d76014, d93612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q hb ha
  have h3 (q : Pattern) (ha : d76059 q = 1) (hb : d93613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76059, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76059, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76061 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76062 q = 1) (hb : d93614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76062, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76062, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76077 q = 1) (hb : d93615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76077, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76077, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76078 q = 1) (hb : d93616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76078, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76078, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76079 q = 1) (hb : d94056 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76079, d94056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76079, d94056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21768 (p : Pattern) (ha : d76120 p = 1) (hb : d94067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76108 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d76113 q = 1) (hb : d94062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76113, d94062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19039 q hb ha
    | true =>
      simp only [d76113, d94062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro170 q hb ha
  have h3 (q : Pattern) (ha : d76114 q = 1) (hb : d94063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76114, d94063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76114, d94063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76116 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76117 q = 1) (hb : d94064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76117, d94064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76117, d94064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76118 q = 1) (hb : d94065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76118, d94065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76118, d94065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76119 q = 1) (hb : d94066 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76119, d94066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76119, d94066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76120 q = 1) (hb : d94067 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76120, d94067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76120, d94067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21769 (p : Pattern) (ha : d76126 p = 1) (hb : d94073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76022 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76066 q = 1) (hb : d93618 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76066, d93618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21765 q ha hb
    | true =>
      simp only [d76066, d93618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21766 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76073 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76074 q = 1) (hb : d93619 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76074, d93619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76074, d93619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76075 q = 1) (hb : d94054 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76075, d94054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76075, d94054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76076 q = 1) (hb : d94055 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76076, d94055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76076, d94055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76080 q = 1) (hb : d94057 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76080, d94057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d76080, d94057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21767 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d76081 q = 1) (hb : d94058 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76081, d94058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76081, d94058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d76082 q = 1) (hb : d94059 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76082, d94059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76082, d94059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d76083 q = 1) (hb : d94060 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76083, d94060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76083, d94060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d76084 q = 1) (hb : d94061 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76084, d94061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76084, d94061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76121 q = 1) (hb : d94068 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76121, d94068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d76121, d94068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21768 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76122 q = 1) (hb : d94069 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76122, d94069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76122, d94069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76123 q = 1) (hb : d94070 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76123, d94070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76123, d94070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d76124 q = 1) (hb : d94071 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76124, d94071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76124, d94071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d76125 q = 1) (hb : d94072 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76125, d94072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76125, d94072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d76126 q = 1) (hb : d94073 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76126, d94073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76126, d94073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro21770 (p : Pattern) (ha : d76132 p = 1) (hb : d94079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76127 q = 1) (hb : d94074 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76127, d94074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76127, d94074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21769 q ha hb
  have h2 (q : Pattern) (ha : d76128 q = 1) (hb : d94075 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76128, d94075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76128, d94075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76129 q = 1) (hb : d94076 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76129, d94076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76129, d94076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76130 q = 1) (hb : d94077 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76130, d94077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76130, d94077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76131 q = 1) (hb : d94078 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76131, d94078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76131, d94078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76132 q = 1) (hb : d94079 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76132, d94079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76132, d94079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21771 (p : Pattern) (ha : d76181 p = 1) (hb : d93717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76163 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76169 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d76174 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d76140 q = 1) (hb : d93712 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76140, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19055 q hb ha
    | true =>
      simp only [d76140, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h5 (q : Pattern) (ha : d76175 q = 1) (hb : d93713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76175, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d76175, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d76177 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d76178 q = 1) (hb : d93714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76178, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76178, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d76179 q = 1) (hb : d93715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76179, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76179, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76180 q = 1) (hb : d93716 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76180, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76180, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76181 q = 1) (hb : d93717 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76181, d93717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76181, d93717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro21772 (p : Pattern) (ha : d76200 p = 1) (hb : d93725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76163 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76169 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76174 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76140 q = 1) (hb : d93712 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76140, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19055 q hb ha
    | true =>
      simp only [d76140, d93712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h4 (q : Pattern) (ha : d76175 q = 1) (hb : d93713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76175, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76175, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76177 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76178 q = 1) (hb : d93714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76178, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76178, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76179 q = 1) (hb : d93715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76179, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76179, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76180 q = 1) (hb : d93716 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76180, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76180, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d76186 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d76190 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d76193 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d76149 q = 1) (hb : d93720 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76149, d93720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19061 q hb ha
    | true =>
      simp only [d76149, d93720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q hb ha
  have h13 (q : Pattern) (ha : d76194 q = 1) (hb : d93721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76194, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d76194, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d76196 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76197 q = 1) (hb : d93722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76197, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76197, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76198 q = 1) (hb : d93723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76198, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d76198, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76199 q = 1) (hb : d93724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76199, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d76199, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76200 q = 1) (hb : d93725 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76200, d93725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76200, d93725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro21773 (p : Pattern) (ha : d76214 p = 1) (hb : d94085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76193 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d76149 q = 1) (hb : d93720 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76149, d93720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19061 q hb ha
    | true =>
      simp only [d76149, d93720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q hb ha
  have h3 (q : Pattern) (ha : d76194 q = 1) (hb : d93721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76194, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76194, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76196 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76197 q = 1) (hb : d93722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76197, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76197, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76212 q = 1) (hb : d93723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76212, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76212, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76213 q = 1) (hb : d93724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76213, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76213, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76214 q = 1) (hb : d94085 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76214, d94085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76214, d94085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21774 (p : Pattern) (ha : d76255 p = 1) (hb : d94096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76243 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d76248 q = 1) (hb : d94091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76248, d94091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19069 q hb ha
    | true =>
      simp only [d76248, d94091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro228 q hb ha
  have h3 (q : Pattern) (ha : d76249 q = 1) (hb : d94092 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76249, d94092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76249, d94092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76251 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76252 q = 1) (hb : d94093 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76252, d94093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76252, d94093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76253 q = 1) (hb : d94094 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76253, d94094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76253, d94094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76254 q = 1) (hb : d94095 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76254, d94095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76254, d94095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76255 q = 1) (hb : d94096 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76255, d94096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76255, d94096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21775 (p : Pattern) (ha : d76261 p = 1) (hb : d94102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76157 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76201 q = 1) (hb : d93726 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76201, d93726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21771 q ha hb
    | true =>
      simp only [d76201, d93726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21772 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76208 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76209 q = 1) (hb : d93727 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76209, d93727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76209, d93727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76210 q = 1) (hb : d94083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76210, d94083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76210, d94083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76211 q = 1) (hb : d94084 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76211, d94084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76211, d94084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76215 q = 1) (hb : d94086 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76215, d94086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d76215, d94086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21773 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d76216 q = 1) (hb : d94087 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76216, d94087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76216, d94087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d76217 q = 1) (hb : d94088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76217, d94088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76217, d94088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d76218 q = 1) (hb : d94089 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76218, d94089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76218, d94089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d76219 q = 1) (hb : d94090 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76219, d94090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76219, d94090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76256 q = 1) (hb : d94097 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76256, d94097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d76256, d94097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21774 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76257 q = 1) (hb : d94098 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76257, d94098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76257, d94098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76258 q = 1) (hb : d94099 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76258, d94099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76258, d94099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d76259 q = 1) (hb : d94100 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76259, d94100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76259, d94100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d76260 q = 1) (hb : d94101 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76260, d94101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76260, d94101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d76261 q = 1) (hb : d94102 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76261, d94102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76261, d94102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro21776 (p : Pattern) (ha : d76267 p = 1) (hb : d94108 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76262 q = 1) (hb : d94103 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76262, d94103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76262, d94103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21775 q ha hb
  have h2 (q : Pattern) (ha : d76263 q = 1) (hb : d94104 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76263, d94104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76263, d94104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76264 q = 1) (hb : d94105 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76264, d94105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76264, d94105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76265 q = 1) (hb : d94106 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76265, d94106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76265, d94106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76266 q = 1) (hb : d94107 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76266, d94107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76266, d94107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76267 q = 1) (hb : d94108 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76267, d94108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76267, d94108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21777 (p : Pattern) (ha : d76317 p = 1) (hb : d93826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76299 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76305 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d76310 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d76276 q = 1) (hb : d93821 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76276, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19085 q hb ha
    | true =>
      simp only [d76276, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h5 (q : Pattern) (ha : d76311 q = 1) (hb : d93822 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76311, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d76311, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d76313 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d76314 q = 1) (hb : d93823 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76314, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76314, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d76315 q = 1) (hb : d93824 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76315, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76315, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76316 q = 1) (hb : d93825 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76316, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76316, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76317 q = 1) (hb : d93826 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76317, d93826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76317, d93826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro21778 (p : Pattern) (ha : d76336 p = 1) (hb : d93834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76305 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76310 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76276 q = 1) (hb : d93821 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76276, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19085 q hb ha
    | true =>
      simp only [d76276, d93821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h4 (q : Pattern) (ha : d76311 q = 1) (hb : d93822 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76311, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76311, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76314 q = 1) (hb : d93823 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76314, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76314, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76315 q = 1) (hb : d93824 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76315, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76315, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76316 q = 1) (hb : d93825 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76316, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76316, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d76322 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d76326 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d76329 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d76285 q = 1) (hb : d93829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76285, d93829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19091 q hb ha
    | true =>
      simp only [d76285, d93829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q hb ha
  have h13 (q : Pattern) (ha : d76330 q = 1) (hb : d93830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76330, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d76330, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d76332 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76333 q = 1) (hb : d93831 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76333, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76333, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76334 q = 1) (hb : d93832 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76334, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d76334, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76335 q = 1) (hb : d93833 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76335, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d76335, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76336 q = 1) (hb : d93834 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76336, d93834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76336, d93834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro21779 (p : Pattern) (ha : d76350 p = 1) (hb : d94115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76329 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d76285 q = 1) (hb : d93829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76285, d93829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19091 q hb ha
    | true =>
      simp only [d76285, d93829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q hb ha
  have h3 (q : Pattern) (ha : d76330 q = 1) (hb : d93830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76330, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76330, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76332 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76333 q = 1) (hb : d93831 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76333, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76333, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76348 q = 1) (hb : d93832 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76348, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76348, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76349 q = 1) (hb : d93833 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76349, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76349, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76350 q = 1) (hb : d94115 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76350, d94115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76350, d94115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21780 (p : Pattern) (ha : d76391 p = 1) (hb : d94126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76379 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d76384 q = 1) (hb : d94121 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76384, d94121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19099 q hb ha
    | true =>
      simp only [d76384, d94121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro287 q hb ha
  have h3 (q : Pattern) (ha : d76385 q = 1) (hb : d94122 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76385, d94122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76385, d94122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d76387 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76388 q = 1) (hb : d94123 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76388, d94123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76388, d94123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76389 q = 1) (hb : d94124 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76389, d94124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76389, d94124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76390 q = 1) (hb : d94125 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76390, d94125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76390, d94125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76391 q = 1) (hb : d94126 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76391, d94126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76391, d94126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21781 (p : Pattern) (ha : d76397 p = 1) (hb : d94132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76293 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76337 q = 1) (hb : d93835 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76337, d93835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21777 q ha hb
    | true =>
      simp only [d76337, d93835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21778 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76345 q = 1) (hb : d93836 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76345, d93836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76345, d93836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76346 q = 1) (hb : d94113 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76346, d94113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76346, d94113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76347 q = 1) (hb : d94114 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76347, d94114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76347, d94114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76351 q = 1) (hb : d94116 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76351, d94116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d76351, d94116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21779 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d76352 q = 1) (hb : d94117 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76352, d94117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76352, d94117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d76353 q = 1) (hb : d94118 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76353, d94118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76353, d94118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d76354 q = 1) (hb : d94119 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76354, d94119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76354, d94119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d76355 q = 1) (hb : d94120 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76355, d94120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76355, d94120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76392 q = 1) (hb : d94127 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76392, d94127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d76392, d94127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21780 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76393 q = 1) (hb : d94128 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76393, d94128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76393, d94128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76394 q = 1) (hb : d94129 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76394, d94129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76394, d94129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d76395 q = 1) (hb : d94130 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76395, d94130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76395, d94130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d76396 q = 1) (hb : d94131 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76396, d94131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76396, d94131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d76397 q = 1) (hb : d94132 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76397, d94132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76397, d94132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro21782 (p : Pattern) (ha : d76403 p = 1) (hb : d94138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76398 q = 1) (hb : d94133 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76398, d94133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76398, d94133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21781 q ha hb
  have h2 (q : Pattern) (ha : d76399 q = 1) (hb : d94134 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76399, d94134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76399, d94134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76400 q = 1) (hb : d94135 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76400, d94135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76400, d94135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76401 q = 1) (hb : d94136 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76401, d94136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76401, d94136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76402 q = 1) (hb : d94137 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76402, d94137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76402, d94137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76403 q = 1) (hb : d94138 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76403, d94138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76403, d94138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21783 (p : Pattern) (ha : d76409 p = 1) (hb : d94144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d75872 q = 1) (hb : d94025 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d75872, d94025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21752 q ha hb
    | true =>
      simp only [d75872, d94025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21758 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d75999 q = 1) (hb : d94052 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d75999, d94052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75999, d94052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21764 q ha hb
  have h3 (q : Pattern) (ha : d76000 q = 1) (hb : d94053 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76000, d94053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76000, d94053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76133 q = 1) (hb : d94080 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76133, d94080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76133, d94080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21770 q ha hb
  have h5 (q : Pattern) (ha : d76134 q = 1) (hb : d94081 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76134, d94081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76134, d94081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76135 q = 1) (hb : d94082 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d76135, d94082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76135, d94082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76268 q = 1) (hb : d94109 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76268, d94109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76268, d94109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21776 q ha hb
  have h8 (q : Pattern) (ha : d76269 q = 1) (hb : d94110 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76269, d94110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76269, d94110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76270 q = 1) (hb : d94111 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d76270, d94111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76270, d94111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76271 q = 1) (hb : d94112 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d76271, d94112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76271, d94112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76404 q = 1) (hb : d94139 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76404, d94139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76404, d94139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21782 q ha hb
  have h12 (q : Pattern) (ha : d76405 q = 1) (hb : d94140 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76405, d94140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76405, d94140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76406 q = 1) (hb : d94141 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d76406, d94141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76406, d94141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76407 q = 1) (hb : d94142 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d76407, d94142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76407, d94142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76408 q = 1) (hb : d94143 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d76408, d94143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76408, d94143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76409 q = 1) (hb : d94144 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d76409, d94144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76409, d94144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro21784 (p : Pattern) (ha : d76415 p = 1) (hb : d94150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76410 q = 1) (hb : d94145 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d76410, d94145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21783 q ha hb
    | true =>
      simp only [d76410, d94145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76411 q = 1) (hb : d94146 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d76411, d94146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76411, d94146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76412 q = 1) (hb : d94147 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d76412, d94147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76412, d94147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76413 q = 1) (hb : d94148 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d76413, d94148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76413, d94148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76414 q = 1) (hb : d94149 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d76414, d94149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76414, d94149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76415 q = 1) (hb : d94150 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d76415, d94150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76415, d94150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21785 (p : Pattern) (ha : d76421 p = 1) (hb : d94156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76416 q = 1) (hb : d94151 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d76416, d94151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21784 q ha hb
    | true =>
      simp only [d76416, d94151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76417 q = 1) (hb : d94152 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d76417, d94152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76417, d94152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76418 q = 1) (hb : d94153 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d76418, d94153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76418, d94153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76419 q = 1) (hb : d94154 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d76419, d94154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76419, d94154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76420 q = 1) (hb : d94155 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d76420, d94155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76420, d94155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76421 q = 1) (hb : d94156 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d76421, d94156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76421, d94156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21786 (p : Pattern) (ha : d76427 p = 1) (hb : d94162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76422 q = 1) (hb : d94157 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d76422, d94157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21785 q ha hb
    | true =>
      simp only [d76422, d94157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76423 q = 1) (hb : d94158 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d76423, d94158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76423, d94158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76424 q = 1) (hb : d94159 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d76424, d94159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76424, d94159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76425 q = 1) (hb : d94160 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d76425, d94160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76425, d94160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76426 q = 1) (hb : d94161 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d76426, d94161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76426, d94161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76427 q = 1) (hb : d94162 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d76427, d94162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76427, d94162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21787 (p : Pattern) (ha : d76433 p = 1) (hb : d94168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76428 q = 1) (hb : d94163 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d76428, d94163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21786 q ha hb
    | true =>
      simp only [d76428, d94163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76429 q = 1) (hb : d94164 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d76429, d94164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76429, d94164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76430 q = 1) (hb : d94165 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d76430, d94165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76430, d94165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76431 q = 1) (hb : d94166 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d76431, d94166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76431, d94166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76432 q = 1) (hb : d94167 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d76432, d94167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76432, d94167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76433 q = 1) (hb : d94168 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d76433, d94168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76433, d94168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21788 (p : Pattern) (ha : d76439 p = 1) (hb : d94174 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76434 q = 1) (hb : d94169 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d76434, d94169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21787 q ha hb
    | true =>
      simp only [d76434, d94169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76435 q = 1) (hb : d94170 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d76435, d94170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76435, d94170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76436 q = 1) (hb : d94171 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d76436, d94171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76436, d94171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76437 q = 1) (hb : d94172 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d76437, d94172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76437, d94172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76438 q = 1) (hb : d94173 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d76438, d94173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76438, d94173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76439 q = 1) (hb : d94174 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d76439, d94174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76439, d94174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21789 (p : Pattern) (ha : d76445 p = 1) (hb : d94180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76440 q = 1) (hb : d94175 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d76440, d94175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21788 q ha hb
    | true =>
      simp only [d76440, d94175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76441 q = 1) (hb : d94176 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d76441, d94176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76441, d94176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76442 q = 1) (hb : d94177 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d76442, d94177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76442, d94177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76443 q = 1) (hb : d94178 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d76443, d94178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76443, d94178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76444 q = 1) (hb : d94179 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d76444, d94179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76444, d94179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76445 q = 1) (hb : d94180 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d76445, d94180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76445, d94180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21790 (p : Pattern) (ha : d76451 p = 1) (hb : d94186 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76446 q = 1) (hb : d94181 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d76446, d94181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21789 q ha hb
    | true =>
      simp only [d76446, d94181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76447 q = 1) (hb : d94182 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d76447, d94182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76447, d94182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76448 q = 1) (hb : d94183 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d76448, d94183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76448, d94183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76449 q = 1) (hb : d94184 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d76449, d94184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76449, d94184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76450 q = 1) (hb : d94185 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d76450, d94185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76450, d94185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76451 q = 1) (hb : d94186 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d76451, d94186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76451, d94186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro21791 (p : Pattern) (ha : d76825 p = 1) (hb : d93315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5911 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5917 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5922 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93270 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76821 q = 1) (hb : d93311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76821, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d76821, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d76822 q = 1) (hb : d93312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76822, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76822, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d76823 q = 1) (hb : d93313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76823, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76823, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76824 q = 1) (hb : d93314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76824, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76824, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76825 q = 1) (hb : d93315 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76825, d93315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76825, d93315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro21792 (p : Pattern) (ha : d76830 p = 1) (hb : d93322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5911 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5917 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5922 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d93270 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d76821 q = 1) (hb : d93311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76821, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76821, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76822 q = 1) (hb : d93312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76822, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76822, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76823 q = 1) (hb : d93313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76823, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76823, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76824 q = 1) (hb : d93314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76824, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76824, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d5937 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5941 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d5943 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d93276 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d76826 q = 1) (hb : d93318 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76826, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d76826, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76827 q = 1) (hb : d93319 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76827, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76827, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76828 q = 1) (hb : d93320 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76828, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d76828, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76829 q = 1) (hb : d93321 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76829, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d76829, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76830 q = 1) (hb : d93322 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76830, d93322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76830, d93322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro21793 (p : Pattern) (ha : d76837 p = 1) (hb : d93976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5943 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93276 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76826 q = 1) (hb : d93318 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76826, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76826, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76827 q = 1) (hb : d93319 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76827, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76827, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76835 q = 1) (hb : d93320 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76835, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76835, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76836 q = 1) (hb : d93321 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76836, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76836, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76837 q = 1) (hb : d93976 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76837, d93976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76837, d93976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21794 (p : Pattern) (ha : d76847 p = 1) (hb : d93986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5969 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93294 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76843 q = 1) (hb : d93982 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76843, d93982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76843, d93982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5379 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76844 q = 1) (hb : d93983 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76844, d93983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76844, d93983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76845 q = 1) (hb : d93984 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76845, d93984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76845, d93984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76846 q = 1) (hb : d93985 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76846, d93985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76846, d93985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76847 q = 1) (hb : d93986 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76847, d93986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76847, d93986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21795 (p : Pattern) (ha : d76853 p = 1) (hb : d93992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5905 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76831 q = 1) (hb : d93323 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76831, d93323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21791 q ha hb
    | true =>
      simp only [d76831, d93323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21792 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5953 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76832 q = 1) (hb : d93324 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76832, d93324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76832, d93324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76833 q = 1) (hb : d93974 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76833, d93974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76833, d93974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76834 q = 1) (hb : d93975 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76834, d93975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76834, d93975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76838 q = 1) (hb : d93977 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76838, d93977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76838, d93977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21793 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d76839 q = 1) (hb : d93978 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76839, d93978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76839, d93978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d76840 q = 1) (hb : d93979 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76840, d93979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76840, d93979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d76841 q = 1) (hb : d93980 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76841, d93980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76841, d93980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d76842 q = 1) (hb : d93981 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76842, d93981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76842, d93981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76848 q = 1) (hb : d93987 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76848, d93987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76848, d93987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21794 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76849 q = 1) (hb : d93988 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76849, d93988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76849, d93988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76850 q = 1) (hb : d93989 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76850, d93989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76850, d93989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d76851 q = 1) (hb : d93990 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76851, d93990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76851, d93990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d76852 q = 1) (hb : d93991 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76852, d93991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76852, d93991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d76853 q = 1) (hb : d93992 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76853, d93992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76853, d93992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro21796 (p : Pattern) (ha : d76859 p = 1) (hb : d93998 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d76854 q = 1) (hb : d93993 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76854, d93993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76854, d93993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21795 q ha hb
  have h8 (q : Pattern) (ha : d76855 q = 1) (hb : d93994 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76855, d93994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76855, d93994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76856 q = 1) (hb : d93995 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76856, d93995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76856, d93995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76857 q = 1) (hb : d93996 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76857, d93996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76857, d93996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76858 q = 1) (hb : d93997 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76858, d93997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76858, d93997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d76859 q = 1) (hb : d93998 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76859, d93998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d76859, d93998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro21797 (p : Pattern) (ha : d76864 p = 1) (hb : d93396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6014 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6020 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6025 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93391 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76860 q = 1) (hb : d93392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76860, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d76860, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5401 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d76861 q = 1) (hb : d93393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76861, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76861, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d76862 q = 1) (hb : d93394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76862, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76862, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76863 q = 1) (hb : d93395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76863, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76863, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76864 q = 1) (hb : d93396 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76864, d93396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76864, d93396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro21798 (p : Pattern) (ha : d76869 p = 1) (hb : d93404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6020 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6025 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d93391 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d76860 q = 1) (hb : d93392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76860, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76860, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5401 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76861 q = 1) (hb : d93393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76861, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76861, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76862 q = 1) (hb : d93394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76862, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76862, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76863 q = 1) (hb : d93395 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76863, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76863, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d6040 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d6044 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6047 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d93399 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d76865 q = 1) (hb : d93400 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76865, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d76865, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5408 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76866 q = 1) (hb : d93401 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76866, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76866, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76867 q = 1) (hb : d93402 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76867, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d76867, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76868 q = 1) (hb : d93403 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76868, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d76868, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76869 q = 1) (hb : d93404 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76869, d93404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76869, d93404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro21799 (p : Pattern) (ha : d76876 p = 1) (hb : d94001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6047 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93399 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76865 q = 1) (hb : d93400 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76865, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76865, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5408 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76866 q = 1) (hb : d93401 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76866, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76866, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76874 q = 1) (hb : d93402 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76874, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76874, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76875 q = 1) (hb : d93403 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76875, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76875, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76876 q = 1) (hb : d94001 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76876, d94001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76876, d94001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21800 (p : Pattern) (ha : d76886 p = 1) (hb : d94012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6091 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94007 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76882 q = 1) (hb : d94008 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76882, d94008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76882, d94008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5430 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76883 q = 1) (hb : d94009 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76883, d94009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76883, d94009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76884 q = 1) (hb : d94010 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76884, d94010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76884, d94010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76885 q = 1) (hb : d94011 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76885, d94011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76885, d94011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76886 q = 1) (hb : d94012 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76886, d94012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76886, d94012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21801 (p : Pattern) (ha : d76892 p = 1) (hb : d94018 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6008 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76870 q = 1) (hb : d93405 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76870, d93405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21797 q ha hb
    | true =>
      simp only [d76870, d93405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21798 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6062 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76871 q = 1) (hb : d93406 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76871, d93406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76871, d93406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76872 q = 1) (hb : d93999 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76872, d93999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76872, d93999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76873 q = 1) (hb : d94000 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76873, d94000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76873, d94000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76877 q = 1) (hb : d94002 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76877, d94002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76877, d94002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21799 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d76878 q = 1) (hb : d94003 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76878, d94003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76878, d94003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d76879 q = 1) (hb : d94004 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76879, d94004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76879, d94004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d76880 q = 1) (hb : d94005 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76880, d94005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76880, d94005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d76881 q = 1) (hb : d94006 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76881, d94006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76881, d94006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76887 q = 1) (hb : d94013 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76887, d94013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76887, d94013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21800 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76888 q = 1) (hb : d94014 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76888, d94014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76888, d94014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76889 q = 1) (hb : d94015 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76889, d94015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76889, d94015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d76890 q = 1) (hb : d94016 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76890, d94016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76890, d94016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d76891 q = 1) (hb : d94017 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76891, d94017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76891, d94017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d76892 q = 1) (hb : d94018 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76892, d94018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76892, d94018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro21802 (p : Pattern) (ha : d76898 p = 1) (hb : d94024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76893 q = 1) (hb : d94019 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76893, d94019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76893, d94019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21801 q ha hb
  have h2 (q : Pattern) (ha : d76894 q = 1) (hb : d94020 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76894, d94020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76894, d94020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76895 q = 1) (hb : d94021 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76895, d94021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76895, d94021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76896 q = 1) (hb : d94022 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76896, d94022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76896, d94022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76897 q = 1) (hb : d94023 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76897, d94023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76897, d94023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76898 q = 1) (hb : d94024 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76898, d94024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76898, d94024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21803 (p : Pattern) (ha : d76904 p = 1) (hb : d93502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6142 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6148 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6153 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93497 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76900 q = 1) (hb : d93498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76900, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d76900, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6161 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d76901 q = 1) (hb : d93499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76901, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76901, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d76902 q = 1) (hb : d93500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76902, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76902, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76903 q = 1) (hb : d93501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76903, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76903, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76904 q = 1) (hb : d93502 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76904, d93502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76904, d93502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro21804 (p : Pattern) (ha : d76909 p = 1) (hb : d93510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6142 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6148 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6153 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d93497 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d76900 q = 1) (hb : d93498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76900, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76900, d93498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6161 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76901 q = 1) (hb : d93499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76901, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76901, d93499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76902 q = 1) (hb : d93500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76902, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76902, d93500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76903 q = 1) (hb : d93501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76903, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76903, d93501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d6170 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d6174 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6177 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d93505 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d76905 q = 1) (hb : d93506 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76905, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d76905, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6182 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76906 q = 1) (hb : d93507 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76906, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76906, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76907 q = 1) (hb : d93508 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76907, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d76907, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76908 q = 1) (hb : d93509 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76908, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d76908, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76909 q = 1) (hb : d93510 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76909, d93510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76909, d93510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro21805 (p : Pattern) (ha : d76916 p = 1) (hb : d94028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6177 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93505 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76905 q = 1) (hb : d93506 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76905, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76905, d93506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6182 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76906 q = 1) (hb : d93507 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76906, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76906, d93507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76914 q = 1) (hb : d93508 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76914, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76914, d93508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76915 q = 1) (hb : d93509 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76915, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76915, d93509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76916 q = 1) (hb : d94028 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76916, d94028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76916, d94028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21806 (p : Pattern) (ha : d76926 p = 1) (hb : d94039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6223 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94034 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76922 q = 1) (hb : d94035 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76922, d94035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76922, d94035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6235 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76923 q = 1) (hb : d94036 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76923, d94036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76923, d94036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76924 q = 1) (hb : d94037 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76924, d94037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76924, d94037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76925 q = 1) (hb : d94038 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76925, d94038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76925, d94038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76926 q = 1) (hb : d94039 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76926, d94039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76926, d94039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21807 (p : Pattern) (ha : d76932 p = 1) (hb : d94045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6136 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76910 q = 1) (hb : d93511 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76910, d93511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21803 q ha hb
    | true =>
      simp only [d76910, d93511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21804 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6194 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76911 q = 1) (hb : d93512 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76911, d93512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76911, d93512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76912 q = 1) (hb : d94026 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76912, d94026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76912, d94026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76913 q = 1) (hb : d94027 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76913, d94027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76913, d94027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76917 q = 1) (hb : d94029 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76917, d94029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76917, d94029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21805 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d76918 q = 1) (hb : d94030 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76918, d94030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76918, d94030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d76919 q = 1) (hb : d94031 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76919, d94031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76919, d94031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d76920 q = 1) (hb : d94032 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76920, d94032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76920, d94032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d76921 q = 1) (hb : d94033 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76921, d94033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76921, d94033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76927 q = 1) (hb : d94040 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76927, d94040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76927, d94040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21806 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76928 q = 1) (hb : d94041 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76928, d94041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76928, d94041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76929 q = 1) (hb : d94042 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76929, d94042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76929, d94042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d76930 q = 1) (hb : d94043 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76930, d94043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76930, d94043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d76931 q = 1) (hb : d94044 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76931, d94044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76931, d94044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d76932 q = 1) (hb : d94045 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76932, d94045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76932, d94045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro21808 (p : Pattern) (ha : d76938 p = 1) (hb : d94051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76933 q = 1) (hb : d94046 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76933, d94046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76933, d94046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21807 q ha hb
  have h2 (q : Pattern) (ha : d76934 q = 1) (hb : d94047 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76934, d94047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76934, d94047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76935 q = 1) (hb : d94048 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76935, d94048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76935, d94048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76936 q = 1) (hb : d94049 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76936, d94049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76936, d94049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76937 q = 1) (hb : d94050 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76937, d94050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76937, d94050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76938 q = 1) (hb : d94051 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76938, d94051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76938, d94051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21809 (p : Pattern) (ha : d76945 p = 1) (hb : d93609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6281 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6287 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6292 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93604 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76941 q = 1) (hb : d93605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76941, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d76941, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6300 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d76942 q = 1) (hb : d93606 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76942, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76942, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d76943 q = 1) (hb : d93607 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76943, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76943, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76944 q = 1) (hb : d93608 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76944, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76944, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76945 q = 1) (hb : d93609 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76945, d93609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76945, d93609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro21810 (p : Pattern) (ha : d76950 p = 1) (hb : d93617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6281 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6287 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6292 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d93604 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d76941 q = 1) (hb : d93605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76941, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76941, d93605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6300 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76942 q = 1) (hb : d93606 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76942, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76942, d93606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76943 q = 1) (hb : d93607 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76943, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76943, d93607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76944 q = 1) (hb : d93608 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76944, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76944, d93608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d6309 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d6313 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6316 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d93612 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d76946 q = 1) (hb : d93613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76946, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d76946, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6321 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76947 q = 1) (hb : d93614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76947, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76947, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76948 q = 1) (hb : d93615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76948, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d76948, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76949 q = 1) (hb : d93616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76949, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d76949, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76950 q = 1) (hb : d93617 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76950, d93617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76950, d93617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro21811 (p : Pattern) (ha : d76957 p = 1) (hb : d94056 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6316 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93612 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76946 q = 1) (hb : d93613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76946, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76946, d93613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6321 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76947 q = 1) (hb : d93614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76947, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76947, d93614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76955 q = 1) (hb : d93615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76955, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76955, d93615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76956 q = 1) (hb : d93616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76956, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76956, d93616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76957 q = 1) (hb : d94056 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76957, d94056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76957, d94056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21812 (p : Pattern) (ha : d76967 p = 1) (hb : d94067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6368 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94062 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76963 q = 1) (hb : d94063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76963, d94063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76963, d94063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6380 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76964 q = 1) (hb : d94064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76964, d94064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76964, d94064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76965 q = 1) (hb : d94065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76965, d94065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76965, d94065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76966 q = 1) (hb : d94066 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76966, d94066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76966, d94066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76967 q = 1) (hb : d94067 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76967, d94067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76967, d94067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21813 (p : Pattern) (ha : d76973 p = 1) (hb : d94073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6275 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76951 q = 1) (hb : d93618 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76951, d93618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21809 q ha hb
    | true =>
      simp only [d76951, d93618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21810 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6333 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76952 q = 1) (hb : d93619 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76952, d93619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76952, d93619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76953 q = 1) (hb : d94054 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76953, d94054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76953, d94054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76954 q = 1) (hb : d94055 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76954, d94055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76954, d94055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76958 q = 1) (hb : d94057 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76958, d94057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76958, d94057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21811 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d76959 q = 1) (hb : d94058 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76959, d94058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76959, d94058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d76960 q = 1) (hb : d94059 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76960, d94059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76960, d94059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d76961 q = 1) (hb : d94060 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76961, d94060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76961, d94060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d76962 q = 1) (hb : d94061 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76962, d94061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76962, d94061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76968 q = 1) (hb : d94068 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76968, d94068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76968, d94068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21812 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1504 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76969 q = 1) (hb : d94069 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76969, d94069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76969, d94069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76970 q = 1) (hb : d94070 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76970, d94070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76970, d94070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d76971 q = 1) (hb : d94071 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76971, d94071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76971, d94071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d76972 q = 1) (hb : d94072 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76972, d94072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76972, d94072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d76973 q = 1) (hb : d94073 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76973, d94073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76973, d94073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro21814 (p : Pattern) (ha : d76979 p = 1) (hb : d94079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76974 q = 1) (hb : d94074 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76974, d94074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76974, d94074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21813 q ha hb
  have h2 (q : Pattern) (ha : d76975 q = 1) (hb : d94075 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76975, d94075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76975, d94075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76976 q = 1) (hb : d94076 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76976, d94076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76976, d94076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76977 q = 1) (hb : d94077 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76977, d94077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76977, d94077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76978 q = 1) (hb : d94078 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76978, d94078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76978, d94078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76979 q = 1) (hb : d94079 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76979, d94079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76979, d94079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21815 (p : Pattern) (ha : d76987 p = 1) (hb : d93717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6427 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6433 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6438 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93712 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76983 q = 1) (hb : d93713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76983, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d76983, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6446 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d76984 q = 1) (hb : d93714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76984, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76984, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d76985 q = 1) (hb : d93715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76985, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76985, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76986 q = 1) (hb : d93716 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76986, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76986, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76987 q = 1) (hb : d93717 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76987, d93717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76987, d93717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro21816 (p : Pattern) (ha : d76992 p = 1) (hb : d93725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6427 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6433 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6438 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d93712 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d76983 q = 1) (hb : d93713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76983, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d76983, d93713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6446 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76984 q = 1) (hb : d93714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76984, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76984, d93714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76985 q = 1) (hb : d93715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76985, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76985, d93715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76986 q = 1) (hb : d93716 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76986, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76986, d93716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d6455 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d6459 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6462 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d93720 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d76988 q = 1) (hb : d93721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76988, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d76988, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6467 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76989 q = 1) (hb : d93722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76989, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76989, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76990 q = 1) (hb : d93723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76990, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d76990, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76991 q = 1) (hb : d93724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76991, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d76991, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76992 q = 1) (hb : d93725 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76992, d93725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76992, d93725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro21817 (p : Pattern) (ha : d76999 p = 1) (hb : d94085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6462 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93720 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76988 q = 1) (hb : d93721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76988, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76988, d93721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6467 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76989 q = 1) (hb : d93722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76989, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76989, d93722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76997 q = 1) (hb : d93723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76997, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76997, d93723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76998 q = 1) (hb : d93724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76998, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76998, d93724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76999 q = 1) (hb : d94085 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76999, d94085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76999, d94085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21818 (p : Pattern) (ha : d77009 p = 1) (hb : d94096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6514 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94091 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77005 q = 1) (hb : d94092 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77005, d94092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d77005, d94092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6526 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77006 q = 1) (hb : d94093 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77006, d94093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77006, d94093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d77007 q = 1) (hb : d94094 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77007, d94094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77007, d94094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77008 q = 1) (hb : d94095 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77008, d94095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77008, d94095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77009 q = 1) (hb : d94096 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77009, d94096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77009, d94096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21819 (p : Pattern) (ha : d77015 p = 1) (hb : d94102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6421 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76993 q = 1) (hb : d93726 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76993, d93726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21815 q ha hb
    | true =>
      simp only [d76993, d93726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21816 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6479 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76994 q = 1) (hb : d93727 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76994, d93727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76994, d93727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76995 q = 1) (hb : d94083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76995, d94083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76995, d94083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76996 q = 1) (hb : d94084 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76996, d94084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76996, d94084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77000 q = 1) (hb : d94086 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77000, d94086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77000, d94086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21817 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1848 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d77001 q = 1) (hb : d94087 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77001, d94087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77001, d94087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d77002 q = 1) (hb : d94088 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77002, d94088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77002, d94088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d77003 q = 1) (hb : d94089 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77003, d94089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77003, d94089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d77004 q = 1) (hb : d94090 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77004, d94090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77004, d94090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77010 q = 1) (hb : d94097 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77010, d94097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77010, d94097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21818 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77011 q = 1) (hb : d94098 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77011, d94098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77011, d94098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d77012 q = 1) (hb : d94099 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77012, d94099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77012, d94099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d77013 q = 1) (hb : d94100 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77013, d94100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77013, d94100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d77014 q = 1) (hb : d94101 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77014, d94101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77014, d94101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d77015 q = 1) (hb : d94102 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77015, d94102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77015, d94102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro21820 (p : Pattern) (ha : d77021 p = 1) (hb : d94108 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77016 q = 1) (hb : d94103 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77016, d94103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77016, d94103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21819 q ha hb
  have h2 (q : Pattern) (ha : d77017 q = 1) (hb : d94104 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77017, d94104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77017, d94104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77018 q = 1) (hb : d94105 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77018, d94105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77018, d94105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77019 q = 1) (hb : d94106 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77019, d94106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77019, d94106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77020 q = 1) (hb : d94107 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77020, d94107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77020, d94107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77021 q = 1) (hb : d94108 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77021, d94108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77021, d94108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21821 (p : Pattern) (ha : d77030 p = 1) (hb : d93826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6574 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6580 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6585 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93821 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77026 q = 1) (hb : d93822 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77026, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d77026, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6593 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d77027 q = 1) (hb : d93823 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77027, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77027, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d77028 q = 1) (hb : d93824 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77028, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d77028, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77029 q = 1) (hb : d93825 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77029, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d77029, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77030 q = 1) (hb : d93826 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77030, d93826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77030, d93826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro21822 (p : Pattern) (ha : d77035 p = 1) (hb : d93834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6580 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6585 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d93821 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d77026 q = 1) (hb : d93822 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77026, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d77026, d93822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6593 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d77027 q = 1) (hb : d93823 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77027, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77027, d93823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d77028 q = 1) (hb : d93824 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77028, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d77028, d93824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77029 q = 1) (hb : d93825 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77029, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77029, d93825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d6602 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d6606 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6609 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d93829 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d77031 q = 1) (hb : d93830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77031, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d77031, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6614 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77032 q = 1) (hb : d93831 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77032, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77032, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d77033 q = 1) (hb : d93832 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77033, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d77033, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77034 q = 1) (hb : d93833 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77034, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d77034, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77035 q = 1) (hb : d93834 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77035, d93834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d77035, d93834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro21823 (p : Pattern) (ha : d77042 p = 1) (hb : d94115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6609 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93829 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77031 q = 1) (hb : d93830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77031, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d77031, d93830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6614 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77032 q = 1) (hb : d93831 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77032, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77032, d93831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d77040 q = 1) (hb : d93832 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77040, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77040, d93832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77041 q = 1) (hb : d93833 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77041, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77041, d93833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77042 q = 1) (hb : d94115 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77042, d94115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77042, d94115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21824 (p : Pattern) (ha : d77052 p = 1) (hb : d94126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6661 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94121 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77048 q = 1) (hb : d94122 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77048, d94122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d77048, d94122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6673 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77049 q = 1) (hb : d94123 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77049, d94123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77049, d94123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d77050 q = 1) (hb : d94124 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77050, d94124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77050, d94124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77051 q = 1) (hb : d94125 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77051, d94125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77051, d94125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77052 q = 1) (hb : d94126 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77052, d94126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77052, d94126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21825 (p : Pattern) (ha : d77058 p = 1) (hb : d94132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6568 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77036 q = 1) (hb : d93835 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77036, d93835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21821 q ha hb
    | true =>
      simp only [d77036, d93835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21822 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6626 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77037 q = 1) (hb : d93836 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77037, d93836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77037, d93836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77038 q = 1) (hb : d94113 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77038, d94113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77038, d94113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77039 q = 1) (hb : d94114 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77039, d94114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77039, d94114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77043 q = 1) (hb : d94116 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77043, d94116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77043, d94116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21823 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2326 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d77044 q = 1) (hb : d94117 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77044, d94117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77044, d94117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d77045 q = 1) (hb : d94118 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77045, d94118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77045, d94118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d77046 q = 1) (hb : d94119 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77046, d94119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77046, d94119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d77047 q = 1) (hb : d94120 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77047, d94120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77047, d94120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77053 q = 1) (hb : d94127 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77053, d94127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77053, d94127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21824 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d2459 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77054 q = 1) (hb : d94128 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77054, d94128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77054, d94128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d77055 q = 1) (hb : d94129 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77055, d94129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77055, d94129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d77056 q = 1) (hb : d94130 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77056, d94130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77056, d94130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d77057 q = 1) (hb : d94131 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77057, d94131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77057, d94131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d77058 q = 1) (hb : d94132 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77058, d94132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77058, d94132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro21826 (p : Pattern) (ha : d77064 p = 1) (hb : d94138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77059 q = 1) (hb : d94133 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77059, d94133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77059, d94133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21825 q ha hb
  have h2 (q : Pattern) (ha : d77060 q = 1) (hb : d94134 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77060, d94134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77060, d94134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77061 q = 1) (hb : d94135 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77061, d94135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77061, d94135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77062 q = 1) (hb : d94136 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77062, d94136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77062, d94136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77063 q = 1) (hb : d94137 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77063, d94137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77063, d94137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77064 q = 1) (hb : d94138 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77064, d94138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77064, d94138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21827 (p : Pattern) (ha : d77070 p = 1) (hb : d94144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d76899 q = 1) (hb : d94025 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76899, d94025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21796 q ha hb
    | true =>
      simp only [d76899, d94025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21802 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d76939 q = 1) (hb : d94052 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76939, d94052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76939, d94052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21808 q ha hb
  have h3 (q : Pattern) (ha : d76940 q = 1) (hb : d94053 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76940, d94053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76940, d94053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76980 q = 1) (hb : d94080 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76980, d94080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76980, d94080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21814 q ha hb
  have h5 (q : Pattern) (ha : d76981 q = 1) (hb : d94081 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76981, d94081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76981, d94081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76982 q = 1) (hb : d94082 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d76982, d94082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76982, d94082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77022 q = 1) (hb : d94109 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77022, d94109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77022, d94109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21820 q ha hb
  have h8 (q : Pattern) (ha : d77023 q = 1) (hb : d94110 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77023, d94110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77023, d94110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77024 q = 1) (hb : d94111 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77024, d94111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77024, d94111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77025 q = 1) (hb : d94112 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d77025, d94112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77025, d94112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77065 q = 1) (hb : d94139 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77065, d94139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77065, d94139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21826 q ha hb
  have h12 (q : Pattern) (ha : d77066 q = 1) (hb : d94140 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77066, d94140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77066, d94140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77067 q = 1) (hb : d94141 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77067, d94141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77067, d94141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d77068 q = 1) (hb : d94142 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d77068, d94142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77068, d94142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77069 q = 1) (hb : d94143 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d77069, d94143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77069, d94143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77070 q = 1) (hb : d94144 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d77070, d94144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77070, d94144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro21828 (p : Pattern) (ha : d77076 p = 1) (hb : d94150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77071 q = 1) (hb : d94145 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d77071, d94145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21827 q ha hb
    | true =>
      simp only [d77071, d94145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77072 q = 1) (hb : d94146 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d77072, d94146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77072, d94146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77073 q = 1) (hb : d94147 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d77073, d94147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77073, d94147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77074 q = 1) (hb : d94148 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d77074, d94148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77074, d94148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77075 q = 1) (hb : d94149 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d77075, d94149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77075, d94149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77076 q = 1) (hb : d94150 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d77076, d94150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77076, d94150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21829 (p : Pattern) (ha : d77082 p = 1) (hb : d94156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77077 q = 1) (hb : d94151 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d77077, d94151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21828 q ha hb
    | true =>
      simp only [d77077, d94151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77078 q = 1) (hb : d94152 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d77078, d94152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77078, d94152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77079 q = 1) (hb : d94153 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d77079, d94153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77079, d94153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77080 q = 1) (hb : d94154 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d77080, d94154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77080, d94154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77081 q = 1) (hb : d94155 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d77081, d94155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77081, d94155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77082 q = 1) (hb : d94156 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d77082, d94156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77082, d94156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21830 (p : Pattern) (ha : d77088 p = 1) (hb : d94162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77083 q = 1) (hb : d94157 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d77083, d94157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21829 q ha hb
    | true =>
      simp only [d77083, d94157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77084 q = 1) (hb : d94158 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d77084, d94158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77084, d94158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77085 q = 1) (hb : d94159 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d77085, d94159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77085, d94159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77086 q = 1) (hb : d94160 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d77086, d94160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77086, d94160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77087 q = 1) (hb : d94161 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d77087, d94161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77087, d94161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77088 q = 1) (hb : d94162 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d77088, d94162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77088, d94162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21831 (p : Pattern) (ha : d77094 p = 1) (hb : d94168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77089 q = 1) (hb : d94163 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d77089, d94163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21830 q ha hb
    | true =>
      simp only [d77089, d94163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77090 q = 1) (hb : d94164 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d77090, d94164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77090, d94164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77091 q = 1) (hb : d94165 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d77091, d94165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77091, d94165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77092 q = 1) (hb : d94166 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d77092, d94166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77092, d94166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77093 q = 1) (hb : d94167 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d77093, d94167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77093, d94167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77094 q = 1) (hb : d94168 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d77094, d94168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77094, d94168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21832 (p : Pattern) (ha : d77100 p = 1) (hb : d94174 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77095 q = 1) (hb : d94169 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d77095, d94169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21831 q ha hb
    | true =>
      simp only [d77095, d94169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77096 q = 1) (hb : d94170 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d77096, d94170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77096, d94170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77097 q = 1) (hb : d94171 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d77097, d94171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77097, d94171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77098 q = 1) (hb : d94172 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d77098, d94172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77098, d94172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77099 q = 1) (hb : d94173 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d77099, d94173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77099, d94173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77100 q = 1) (hb : d94174 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d77100, d94174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77100, d94174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21833 (p : Pattern) (ha : d77106 p = 1) (hb : d94180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77101 q = 1) (hb : d94175 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d77101, d94175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21832 q ha hb
    | true =>
      simp only [d77101, d94175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77102 q = 1) (hb : d94176 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d77102, d94176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77102, d94176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77103 q = 1) (hb : d94177 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d77103, d94177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77103, d94177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77104 q = 1) (hb : d94178 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d77104, d94178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77104, d94178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77105 q = 1) (hb : d94179 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d77105, d94179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77105, d94179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77106 q = 1) (hb : d94180 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d77106, d94180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77106, d94180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21834 (p : Pattern) (ha : d77112 p = 1) (hb : d94186 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77107 q = 1) (hb : d94181 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d77107, d94181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21833 q ha hb
    | true =>
      simp only [d77107, d94181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77108 q = 1) (hb : d94182 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d77108, d94182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77108, d94182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77109 q = 1) (hb : d94183 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d77109, d94183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77109, d94183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77110 q = 1) (hb : d94184 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d77110, d94184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77110, d94184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77111 q = 1) (hb : d94185 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d77111, d94185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77111, d94185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77112 q = 1) (hb : d94186 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d77112, d94186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77112, d94186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21835 (p : Pattern) (ha : d144 p = 1) (hb : d122305 p = 1) : d123879 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d142 q = 1) : d142 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d143 q = 1) (hb : d122304 q = 1) : d13980 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d122304, d13980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d143, d122304, d13980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d29 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d144 q = 1) (hb : d122305 q = 1) : d123879 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, d122305, d123879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144, d122305, d123879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro21836 (p : Pattern) (ha : d6739 p = 1) (hb : d122306 p = 1) : d123885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d122305 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d122305 q = 1) : d123880 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21835 q ha hb
    | true =>
      simp only [d145, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d122305 q = 1) : d123881 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d122305 q = 1) : d123882 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d475 q = 1) (hb : d122306 q = 1) : d123883 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d122306, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d475, d122306, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d122306 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6738 q = 1) (hb : d122306 q = 1) : d123884 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6738, d123884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6738, d123884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d6739 q = 1) (hb : d122306 q = 1) : d123885 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6739, d123885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6739, d123885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro21837 (p : Pattern) (ha : d8238 p = 1) (hb : d122306 p = 1) : d123891 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d122306 q = 1) : d123886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21836 q ha hb
    | true =>
      simp only [d6740, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d122306 q = 1) : d123887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122306 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d122306 q = 1) : d123888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8236 q = 1) (hb : d122306 q = 1) : d123889 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8236, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8237 q = 1) (hb : d122306 q = 1) : d123890 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8237, d123890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8237, d123890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8238 q = 1) (hb : d122306 q = 1) : d123891 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8238, d123891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8238, d123891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21838 (p : Pattern) (ha : d94191 p = 1) (hb : d122306 p = 1) : d123897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d122306 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d122306 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d122306 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8239 q = 1) (hb : d122306 q = 1) : d123892 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21837 q ha hb
    | true =>
      simp only [d8239, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94187 q = 1) (hb : d122306 q = 1) : d123893 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94187, d123893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94187, d123893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d122306 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94188 q = 1) (hb : d122306 q = 1) : d123894 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94188, d123894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94188, d123894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94189 q = 1) (hb : d122306 q = 1) : d123895 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94189, d123895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94189, d123895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94190 q = 1) (hb : d122306 q = 1) : d123896 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94190, d123896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94190, d123896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94191 q = 1) (hb : d122306 q = 1) : d123897 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94191, d123897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94191, d123897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro21839 (p : Pattern) (ha : d8245 p = 1) (hb : d122306 p = 1) : d123898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d122306 q = 1) : d123886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21836 q ha hb
    | true =>
      simp only [d6740, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d122306 q = 1) : d123887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122306 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d122306 q = 1) : d123888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8236 q = 1) (hb : d122306 q = 1) : d123889 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8236, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8237 q = 1) (hb : d122306 q = 1) : d123890 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8237, d123890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8237, d123890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8245 q = 1) (hb : d122306 q = 1) : d123898 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8245, d123898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8245, d123898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro21840 (p : Pattern) (ha : d94196 p = 1) (hb : d122306 p = 1) : d123904 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d122306 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d122306 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d122306 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8239 q = 1) (hb : d122306 q = 1) : d123892 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21837 q ha hb
    | true =>
      simp only [d8239, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94187 q = 1) (hb : d122306 q = 1) : d123893 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94187, d123893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94187, d123893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d122306 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94188 q = 1) (hb : d122306 q = 1) : d123894 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94188, d123894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94188, d123894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94189 q = 1) (hb : d122306 q = 1) : d123895 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94189, d123895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94189, d123895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94190 q = 1) (hb : d122306 q = 1) : d123896 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94190, d123896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94190, d123896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d122306 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d122306 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d122306 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8246 q = 1) (hb : d122306 q = 1) : d123899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21839 q ha hb
    | true =>
      simp only [d8246, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94192 q = 1) (hb : d122306 q = 1) : d123900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94192, d123900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94192, d123900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d122306 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d94193 q = 1) (hb : d122306 q = 1) : d123901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94193, d123901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94193, d123901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94194 q = 1) (hb : d122306 q = 1) : d123902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94194, d123902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94194, d123902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94195 q = 1) (hb : d122306 q = 1) : d123903 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94195, d123903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94195, d123903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d94196 q = 1) (hb : d122306 q = 1) : d123904 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94196, d123904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94196, d123904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro21841 (p : Pattern) (ha : d94203 p = 1) (hb : d122306 p = 1) : d123911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d122306 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8246 q = 1) (hb : d122306 q = 1) : d123899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21839 q ha hb
    | true =>
      simp only [d8246, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94192 q = 1) (hb : d122306 q = 1) : d123900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94192, d123900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94192, d123900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d122306 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94193 q = 1) (hb : d122306 q = 1) : d123901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94193, d123901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94193, d123901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94201 q = 1) (hb : d122306 q = 1) : d123909 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94201, d123909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94201, d123909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94202 q = 1) (hb : d122306 q = 1) : d123910 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94202, d123910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94202, d123910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94203 q = 1) (hb : d122306 q = 1) : d123911 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94203, d123911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94203, d123911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21842 (p : Pattern) (ha : d231 p = 1) (hb : d122305 p = 1) : d123917 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d229 q = 1) : d229 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d230 q = 1) (hb : d122304 q = 1) : d14019 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d122304, d14019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d230, d122304, d14019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d231 q = 1) (hb : d122305 q = 1) : d123917 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d122305, d123917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231, d122305, d123917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro21843 (p : Pattern) (ha : d6772 p = 1) (hb : d122306 p = 1) : d123923 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d122305 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d122305 q = 1) : d123918 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21842 q ha hb
    | true =>
      simp only [d232, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d122305 q = 1) : d123919 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d122305 q = 1) : d123920 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d673 q = 1) (hb : d122306 q = 1) : d123921 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d122306, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d673, d122306, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d122306 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6771 q = 1) (hb : d122306 q = 1) : d123922 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6771, d123922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6771, d123922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d6772 q = 1) (hb : d122306 q = 1) : d123923 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6772, d123923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6772, d123923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro21844 (p : Pattern) (ha : d8267 p = 1) (hb : d122306 p = 1) : d123929 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6773 q = 1) (hb : d122306 q = 1) : d123924 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21843 q ha hb
    | true =>
      simp only [d6773, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6774 q = 1) (hb : d122306 q = 1) : d123925 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6774, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6774, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d122306 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8264 q = 1) (hb : d122306 q = 1) : d123926 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8264, d123926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8264, d123926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8265 q = 1) (hb : d122306 q = 1) : d123927 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8265, d123927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8265, d123927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8266 q = 1) (hb : d122306 q = 1) : d123928 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8266, d123928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8266, d123928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8267 q = 1) (hb : d122306 q = 1) : d123929 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8267, d123929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8267, d123929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro21845 (p : Pattern) (ha : d94213 p = 1) (hb : d122306 p = 1) : d123935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d122306 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8268 q = 1) (hb : d122306 q = 1) : d123930 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8268, d123930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21844 q ha hb
    | true =>
      simp only [d8268, d123930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94209 q = 1) (hb : d122306 q = 1) : d123931 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94209, d123931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94209, d123931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d122306 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94210 q = 1) (hb : d122306 q = 1) : d123932 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94210, d123932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94210, d123932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94211 q = 1) (hb : d122306 q = 1) : d123933 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94211, d123933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94211, d123933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94212 q = 1) (hb : d122306 q = 1) : d123934 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94212, d123934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94212, d123934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94213 q = 1) (hb : d122306 q = 1) : d123935 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94213, d123935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94213, d123935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21846 (p : Pattern) (ha : d94219 p = 1) (hb : d122306 p = 1) : d123941 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d122306 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94197 q = 1) (hb : d122306 q = 1) : d123905 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94197, d123905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21838 q ha hb
    | true =>
      simp only [d94197, d123905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21840 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d122306 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94198 q = 1) (hb : d122306 q = 1) : d123906 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94198, d123906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94198, d123906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94199 q = 1) (hb : d122306 q = 1) : d123907 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94199, d123907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94199, d123907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94200 q = 1) (hb : d122306 q = 1) : d123908 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94200, d123908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94200, d123908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94204 q = 1) (hb : d122306 q = 1) : d123912 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94204, d123912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94204, d123912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21841 q ha hb
  have h8 (q : Pattern) (ha : d94205 q = 1) (hb : d122306 q = 1) : d123913 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94205, d123913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94205, d123913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d94206 q = 1) (hb : d122306 q = 1) : d123914 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94206, d123914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94206, d123914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d94207 q = 1) (hb : d122306 q = 1) : d123915 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94207, d123915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94207, d123915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94208 q = 1) (hb : d122306 q = 1) : d123916 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94208, d123916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94208, d123916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d94214 q = 1) (hb : d122306 q = 1) : d123936 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94214, d123936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94214, d123936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21845 q ha hb
  have h13 (q : Pattern) (ha : d94215 q = 1) (hb : d122306 q = 1) : d123937 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94215, d123937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94215, d123937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d94216 q = 1) (hb : d122306 q = 1) : d123938 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94216, d123938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94216, d123938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d94217 q = 1) (hb : d122306 q = 1) : d123939 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94217, d123939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94217, d123939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d94218 q = 1) (hb : d122306 q = 1) : d123940 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94218, d123940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94218, d123940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94219 q = 1) (hb : d122306 q = 1) : d123941 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94219, d123941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94219, d123941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro21847 (p : Pattern) (ha : d8289 p = 1) (hb : d122306 p = 1) : d123951 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d122306 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8239 q = 1) (hb : d122306 q = 1) : d123892 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21837 q ha hb
    | true =>
      simp only [d8239, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8285 q = 1) (hb : d122306 q = 1) : d123947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8285, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8286 q = 1) (hb : d122306 q = 1) : d123948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8286, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8287 q = 1) (hb : d122306 q = 1) : d123949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8287, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8288 q = 1) (hb : d122306 q = 1) : d123950 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8289 q = 1) (hb : d122306 q = 1) : d123951 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8289, d123951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8289, d123951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21848 (p : Pattern) (ha : d8296 p = 1) (hb : d122306 p = 1) : d123958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d122306 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8239 q = 1) (hb : d122306 q = 1) : d123892 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21837 q ha hb
    | true =>
      simp only [d8239, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8285 q = 1) (hb : d122306 q = 1) : d123947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8285, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8286 q = 1) (hb : d122306 q = 1) : d123948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8286, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8287 q = 1) (hb : d122306 q = 1) : d123949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8287, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8288 q = 1) (hb : d122306 q = 1) : d123950 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d122306 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8246 q = 1) (hb : d122306 q = 1) : d123899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21839 q ha hb
    | true =>
      simp only [d8246, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8292 q = 1) (hb : d122306 q = 1) : d123954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8292, d123954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8292, d123954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8293 q = 1) (hb : d122306 q = 1) : d123955 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8293, d123955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8293, d123955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8294 q = 1) (hb : d122306 q = 1) : d123956 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8294, d123956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8294, d123956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d8295 q = 1) (hb : d122306 q = 1) : d123957 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8295, d123957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8295, d123957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d8296 q = 1) (hb : d122306 q = 1) : d123958 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8296, d123958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8296, d123958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro21849 (p : Pattern) (ha : d8363 p = 1) (hb : d122306 p = 1) : d124019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d122306 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8239 q = 1) (hb : d122306 q = 1) : d123892 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21837 q ha hb
    | true =>
      simp only [d8239, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8285 q = 1) (hb : d122306 q = 1) : d123947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8285, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8286 q = 1) (hb : d122306 q = 1) : d123948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8286, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8287 q = 1) (hb : d122306 q = 1) : d123949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8287, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8288 q = 1) (hb : d122306 q = 1) : d123950 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d122306 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8363 q = 1) (hb : d122306 q = 1) : d124019 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8363, d124019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8363, d124019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21850 (p : Pattern) (ha : d8301 p = 1) (hb : d122306 p = 1) : d123963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d122306 q = 1) : d123886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21836 q ha hb
    | true =>
      simp only [d6740, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d122306 q = 1) : d123887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122306 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d122306 q = 1) : d123888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8236 q = 1) (hb : d122306 q = 1) : d123889 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8236, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8300 q = 1) (hb : d122306 q = 1) : d123962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8300, d123962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8300, d123962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8301 q = 1) (hb : d122306 q = 1) : d123963 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8301, d123963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8301, d123963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21851 (p : Pattern) (ha : d8308 p = 1) (hb : d122306 p = 1) : d123970 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d122306 q = 1) : d123886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21836 q ha hb
    | true =>
      simp only [d6740, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d122306 q = 1) : d123887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122306 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d122306 q = 1) : d123888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8306 q = 1) (hb : d122306 q = 1) : d123968 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8306, d123968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8306, d123968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8307 q = 1) (hb : d122306 q = 1) : d123969 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8307, d123969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8307, d123969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8308 q = 1) (hb : d122306 q = 1) : d123970 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8308, d123970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8308, d123970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro21852 (p : Pattern) (ha : d324 p = 1) (hb : d122305 p = 1) : d123974 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d322 q = 1) : d322 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d142 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d323 q = 1) (hb : d122304 q = 1) : d14077 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d122304, d14077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d323, d122304, d14077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d143 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d324 q = 1) (hb : d122305 q = 1) : d123974 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d324, d122305, d123974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324, d122305, d123974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro21853 (p : Pattern) (ha : d8313 p = 1) (hb : d122306 p = 1) : d123980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325 q = 1) (hb : d122305 q = 1) : d123975 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21852 q ha hb
    | true =>
      simp only [d325, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21835 q ha hb
  have h2 (q : Pattern) (ha : d326 q = 1) (hb : d122305 q = 1) : d123976 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d327 q = 1) (hb : d122305 q = 1) : d123977 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6797 q = 1) (hb : d122306 q = 1) : d123978 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6797, d122306, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6797, d122306, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30 q = 1) (hb : d122305 q = 1) : d30 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d145 q = 1) (hb : d122305 q = 1) : d123880 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21835 q ha hb
    | true =>
      simp only [d145, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146 q = 1) (hb : d122305 q = 1) : d123881 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147 q = 1) (hb : d122305 q = 1) : d123882 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d475 q = 1) (hb : d122306 q = 1) : d123883 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d122306, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d475, d122306, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d8312 q = 1) (hb : d122306 q = 1) : d123979 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8312, d123979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8312, d123979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8313 q = 1) (hb : d122306 q = 1) : d123980 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8313, d123980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8313, d123980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro21854 (p : Pattern) (ha : d8319 p = 1) (hb : d122306 p = 1) : d123986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21853 q ha hb
    | true =>
      simp only [d8314, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6740 q = 1) (hb : d122306 q = 1) : d123886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21836 q ha hb
    | true =>
      simp only [d6740, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6741 q = 1) (hb : d122306 q = 1) : d123887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8316 q = 1) (hb : d122306 q = 1) : d123983 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8316, d123983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8316, d123983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8317 q = 1) (hb : d122306 q = 1) : d123984 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8317, d123984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8317, d123984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8318 q = 1) (hb : d122306 q = 1) : d123985 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8318, d123985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8318, d123985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8319 q = 1) (hb : d122306 q = 1) : d123986 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8319, d123986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8319, d123986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21855 (p : Pattern) (ha : d8334 p = 1) (hb : d122306 p = 1) : d123992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d122306 q = 1) : d123886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21836 q ha hb
    | true =>
      simp only [d6740, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d122306 q = 1) : d123887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8331 q = 1) (hb : d122306 q = 1) : d123989 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d123989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d123989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8332 q = 1) (hb : d122306 q = 1) : d123990 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8332, d123990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8332, d123990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8333 q = 1) (hb : d122306 q = 1) : d123991 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8333, d123991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8333, d123991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8334 q = 1) (hb : d122306 q = 1) : d123992 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8334, d123992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8334, d123992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21856 (p : Pattern) (ha : d94229 p = 1) (hb : d122306 p = 1) : d123998 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d122306 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8302 q = 1) (hb : d122306 q = 1) : d123964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8302, d123964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21850 q ha hb
    | true =>
      simp only [d8302, d123964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8303 q = 1) (hb : d122306 q = 1) : d123965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8303, d123965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8303, d123965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8304 q = 1) (hb : d122306 q = 1) : d123966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8304, d123966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8304, d123966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8305 q = 1) (hb : d122306 q = 1) : d123967 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8305, d123967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8305, d123967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d122306 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8309 q = 1) (hb : d122306 q = 1) : d123971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8309, d123971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21851 q ha hb
    | true =>
      simp only [d8309, d123971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8310 q = 1) (hb : d122306 q = 1) : d123972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8310, d123972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8310, d123972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8311 q = 1) (hb : d122306 q = 1) : d123973 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8311, d123973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8311, d123973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8320 q = 1) (hb : d122306 q = 1) : d123987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8320, d123987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21854 q ha hb
    | true =>
      simp only [d8320, d123987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21837 q ha hb
  have h11 (q : Pattern) (ha : d94225 q = 1) (hb : d122306 q = 1) : d123988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94225, d123988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94225, d123988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8335 q = 1) (hb : d122306 q = 1) : d123993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8335, d123993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21855 q ha hb
    | true =>
      simp only [d8335, d123993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d8336 q = 1) (hb : d122306 q = 1) : d123994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8336, d123994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d8336, d123994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94226 q = 1) (hb : d122306 q = 1) : d123995 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94226, d123995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94226, d123995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94227 q = 1) (hb : d122306 q = 1) : d123996 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94227, d123996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94227, d123996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94228 q = 1) (hb : d122306 q = 1) : d123997 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94228, d123997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94228, d123997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94229 q = 1) (hb : d122306 q = 1) : d123998 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94229, d123998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94229, d123998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro21857 (p : Pattern) (ha : d8341 p = 1) (hb : d122306 p = 1) : d123999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d122306 q = 1) : d123886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21836 q ha hb
    | true =>
      simp only [d6740, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d122306 q = 1) : d123887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122306 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d122306 q = 1) : d123888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8236 q = 1) (hb : d122306 q = 1) : d123889 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8236, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8300 q = 1) (hb : d122306 q = 1) : d123962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8300, d123962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8300, d123962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8341 q = 1) (hb : d122306 q = 1) : d123999 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8341, d123999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8341, d123999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro21858 (p : Pattern) (ha : d8346 p = 1) (hb : d122306 p = 1) : d124004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d122306 q = 1) : d123886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21836 q ha hb
    | true =>
      simp only [d6740, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d122306 q = 1) : d123887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122306 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8235 q = 1) (hb : d122306 q = 1) : d123888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8306 q = 1) (hb : d122306 q = 1) : d123968 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8306, d123968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8306, d123968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8307 q = 1) (hb : d122306 q = 1) : d123969 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8307, d123969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8307, d123969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8346 q = 1) (hb : d122306 q = 1) : d124004 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8346, d124004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8346, d124004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro21859 (p : Pattern) (ha : d8350 p = 1) (hb : d122306 p = 1) : d124008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21853 q ha hb
    | true =>
      simp only [d8314, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6740 q = 1) (hb : d122306 q = 1) : d123886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21836 q ha hb
    | true =>
      simp only [d6740, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6741 q = 1) (hb : d122306 q = 1) : d123887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8316 q = 1) (hb : d122306 q = 1) : d123983 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8316, d123983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8316, d123983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8317 q = 1) (hb : d122306 q = 1) : d123984 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8317, d123984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8317, d123984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8318 q = 1) (hb : d122306 q = 1) : d123985 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8318, d123985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8318, d123985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8350 q = 1) (hb : d122306 q = 1) : d124008 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8350, d124008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8350, d124008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro21860 (p : Pattern) (ha : d8355 p = 1) (hb : d122306 p = 1) : d124011 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d122306 q = 1) : d123886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21836 q ha hb
    | true =>
      simp only [d6740, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d122306 q = 1) : d123887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8331 q = 1) (hb : d122306 q = 1) : d123989 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d123989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d123989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8332 q = 1) (hb : d122306 q = 1) : d123990 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8332, d123990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8332, d123990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8333 q = 1) (hb : d122306 q = 1) : d123991 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8333, d123991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8333, d123991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8355 q = 1) (hb : d122306 q = 1) : d124011 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8355, d124011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8355, d124011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21861 (p : Pattern) (ha : d94234 p = 1) (hb : d122306 p = 1) : d124017 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d122306 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8302 q = 1) (hb : d122306 q = 1) : d123964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8302, d123964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21850 q ha hb
    | true =>
      simp only [d8302, d123964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8303 q = 1) (hb : d122306 q = 1) : d123965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8303, d123965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8303, d123965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8304 q = 1) (hb : d122306 q = 1) : d123966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8304, d123966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8304, d123966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8305 q = 1) (hb : d122306 q = 1) : d123967 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8305, d123967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8305, d123967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d122306 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8309 q = 1) (hb : d122306 q = 1) : d123971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8309, d123971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21851 q ha hb
    | true =>
      simp only [d8309, d123971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8310 q = 1) (hb : d122306 q = 1) : d123972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8310, d123972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8310, d123972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8311 q = 1) (hb : d122306 q = 1) : d123973 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8311, d123973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8311, d123973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8320 q = 1) (hb : d122306 q = 1) : d123987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8320, d123987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21854 q ha hb
    | true =>
      simp only [d8320, d123987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21837 q ha hb
  have h11 (q : Pattern) (ha : d94225 q = 1) (hb : d122306 q = 1) : d123988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94225, d123988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94225, d123988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8335 q = 1) (hb : d122306 q = 1) : d123993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8335, d123993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21855 q ha hb
    | true =>
      simp only [d8335, d123993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d8336 q = 1) (hb : d122306 q = 1) : d123994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8336, d123994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d8336, d123994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94226 q = 1) (hb : d122306 q = 1) : d123995 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94226, d123995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94226, d123995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94227 q = 1) (hb : d122306 q = 1) : d123996 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94227, d123996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94227, d123996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94228 q = 1) (hb : d122306 q = 1) : d123997 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94228, d123997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94228, d123997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d122306 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d8342 q = 1) (hb : d122306 q = 1) : d124000 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8342, d124000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21857 q ha hb
    | true =>
      simp only [d8342, d124000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8343 q = 1) (hb : d122306 q = 1) : d124001 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8343, d124001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8343, d124001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d8344 q = 1) (hb : d122306 q = 1) : d124002 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8344, d124002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d8344, d124002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d8345 q = 1) (hb : d122306 q = 1) : d124003 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8345, d124003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8345, d124003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d122306 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d8347 q = 1) (hb : d122306 q = 1) : d124005 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8347, d124005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21858 q ha hb
    | true =>
      simp only [d8347, d124005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d8348 q = 1) (hb : d122306 q = 1) : d124006 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8348, d124006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8348, d124006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d8349 q = 1) (hb : d122306 q = 1) : d124007 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8349, d124007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8349, d124007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d8351 q = 1) (hb : d122306 q = 1) : d124009 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8351, d124009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21859 q ha hb
    | true =>
      simp only [d8351, d124009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21839 q ha hb
  have h27 (q : Pattern) (ha : d94230 q = 1) (hb : d122306 q = 1) : d124010 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94230, d124010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d94230, d124010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d8356 q = 1) (hb : d122306 q = 1) : d124012 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8356, d124012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21860 q ha hb
    | true =>
      simp only [d8356, d124012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d8357 q = 1) (hb : d122306 q = 1) : d124013 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8357, d124013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d8357, d124013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d94231 q = 1) (hb : d122306 q = 1) : d124014 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94231, d124014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d94231, d124014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d94232 q = 1) (hb : d122306 q = 1) : d124015 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94232, d124015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d94232, d124015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d94233 q = 1) (hb : d122306 q = 1) : d124016 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94233, d124016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94233, d124016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d94234 q = 1) (hb : d122306 q = 1) : d124017 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94234, d124017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94234, d124017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro21862 (p : Pattern) (ha : d94241 p = 1) (hb : d122306 p = 1) : d124026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8351 q = 1) (hb : d122306 q = 1) : d124009 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8351, d124009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21859 q ha hb
    | true =>
      simp only [d8351, d124009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21839 q ha hb
  have h2 (q : Pattern) (ha : d94230 q = 1) (hb : d122306 q = 1) : d124010 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94230, d124010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94230, d124010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8356 q = 1) (hb : d122306 q = 1) : d124012 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8356, d124012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21860 q ha hb
    | true =>
      simp only [d8356, d124012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8357 q = 1) (hb : d122306 q = 1) : d124013 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8357, d124013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8357, d124013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94231 q = 1) (hb : d122306 q = 1) : d124014 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94231, d124014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94231, d124014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94239 q = 1) (hb : d122306 q = 1) : d124024 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94239, d124024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94239, d124024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94240 q = 1) (hb : d122306 q = 1) : d124025 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94240, d124025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94240, d124025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94241 q = 1) (hb : d122306 q = 1) : d124026 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94241, d124026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94241, d124026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21863 (p : Pattern) (ha : d417 p = 1) (hb : d122305 p = 1) : d124032 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d415 q = 1) : d415 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d229 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d416 q = 1) (hb : d122304 q = 1) : d14154 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d122304, d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d416, d122304, d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d417 q = 1) (hb : d122305 q = 1) : d124032 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d417, d122305, d124032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d417, d122305, d124032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro21864 (p : Pattern) (ha : d8377 p = 1) (hb : d122306 p = 1) : d124038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d418 q = 1) (hb : d122305 q = 1) : d124033 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21863 q ha hb
    | true =>
      simp only [d418, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21842 q ha hb
  have h2 (q : Pattern) (ha : d419 q = 1) (hb : d122305 q = 1) : d124034 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d420 q = 1) (hb : d122305 q = 1) : d124035 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6843 q = 1) (hb : d122306 q = 1) : d124036 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6843, d122306, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6843, d122306, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71 q = 1) (hb : d122305 q = 1) : d71 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d232 q = 1) (hb : d122305 q = 1) : d123918 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21842 q ha hb
    | true =>
      simp only [d232, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d233 q = 1) (hb : d122305 q = 1) : d123919 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d234 q = 1) (hb : d122305 q = 1) : d123920 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d673 q = 1) (hb : d122306 q = 1) : d123921 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d122306, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d673, d122306, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d8376 q = 1) (hb : d122306 q = 1) : d124037 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8376, d124037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8376, d124037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8377 q = 1) (hb : d122306 q = 1) : d124038 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8377, d124038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8377, d124038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro21865 (p : Pattern) (ha : d8383 p = 1) (hb : d122306 p = 1) : d124044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8378 q = 1) (hb : d122306 q = 1) : d124039 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8378, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21864 q ha hb
    | true =>
      simp only [d8378, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8379 q = 1) (hb : d122306 q = 1) : d124040 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8379, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8379, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6773 q = 1) (hb : d122306 q = 1) : d123924 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21843 q ha hb
    | true =>
      simp only [d6773, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6774 q = 1) (hb : d122306 q = 1) : d123925 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6774, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6774, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8380 q = 1) (hb : d122306 q = 1) : d124041 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8380, d124041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8380, d124041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8381 q = 1) (hb : d122306 q = 1) : d124042 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8381, d124042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8381, d124042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8382 q = 1) (hb : d122306 q = 1) : d124043 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8382, d124043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8382, d124043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8383 q = 1) (hb : d122306 q = 1) : d124044 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8383, d124044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8383, d124044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro21866 (p : Pattern) (ha : d8398 p = 1) (hb : d122306 p = 1) : d124050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6773 q = 1) (hb : d122306 q = 1) : d123924 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21843 q ha hb
    | true =>
      simp only [d6773, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6774 q = 1) (hb : d122306 q = 1) : d123925 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6774, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6774, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8395 q = 1) (hb : d122306 q = 1) : d124047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8395, d124047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8395, d124047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8396 q = 1) (hb : d122306 q = 1) : d124048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8396, d124048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8396, d124048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8397 q = 1) (hb : d122306 q = 1) : d124049 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8397, d124049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8397, d124049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8398 q = 1) (hb : d122306 q = 1) : d124050 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8398, d124050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8398, d124050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21867 (p : Pattern) (ha : d94251 p = 1) (hb : d122306 p = 1) : d124056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8384 q = 1) (hb : d122306 q = 1) : d124045 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8384, d124045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21865 q ha hb
    | true =>
      simp only [d8384, d124045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21844 q ha hb
  have h2 (q : Pattern) (ha : d94247 q = 1) (hb : d122306 q = 1) : d124046 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94247, d124046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94247, d124046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8399 q = 1) (hb : d122306 q = 1) : d124051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8399, d124051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21866 q ha hb
    | true =>
      simp only [d8399, d124051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8400 q = 1) (hb : d122306 q = 1) : d124052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8400, d124052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8400, d124052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94248 q = 1) (hb : d122306 q = 1) : d124053 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94248, d124053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94248, d124053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94249 q = 1) (hb : d122306 q = 1) : d124054 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94249, d124054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94249, d124054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94250 q = 1) (hb : d122306 q = 1) : d124055 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94250, d124055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94250, d124055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94251 q = 1) (hb : d122306 q = 1) : d124056 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94251, d124056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94251, d124056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21868 (p : Pattern) (ha : d94257 p = 1) (hb : d122306 p = 1) : d124062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8290 q = 1) (hb : d122306 q = 1) : d123952 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8290, d123952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8290, d123952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21847 q ha hb
  have h2 (q : Pattern) (ha : d8291 q = 1) (hb : d122306 q = 1) : d123953 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8291, d123953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8291, d123953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8297 q = 1) (hb : d122306 q = 1) : d123959 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8297, d123959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21847 q ha hb
    | true =>
      simp only [d8297, d123959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21848 q ha hb
  have h4 (q : Pattern) (ha : d8298 q = 1) (hb : d122306 q = 1) : d123960 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8298, d123960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8298, d123960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8299 q = 1) (hb : d122306 q = 1) : d123961 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8299, d123961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8299, d123961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94235 q = 1) (hb : d122306 q = 1) : d124018 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94235, d124018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21856 q ha hb
    | true =>
      simp only [d94235, d124018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21861 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d122306 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8364 q = 1) (hb : d122306 q = 1) : d124020 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8364, d124020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21849 q ha hb
    | true =>
      simp only [d8364, d124020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94236 q = 1) (hb : d122306 q = 1) : d124021 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94236, d124021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94236, d124021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94237 q = 1) (hb : d122306 q = 1) : d124022 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94237, d124022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94237, d124022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d94238 q = 1) (hb : d122306 q = 1) : d124023 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94238, d124023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94238, d124023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d94242 q = 1) (hb : d122306 q = 1) : d124027 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94242, d124027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94242, d124027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21862 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d122306 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d94243 q = 1) (hb : d122306 q = 1) : d124028 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94243, d124028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94243, d124028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94244 q = 1) (hb : d122306 q = 1) : d124029 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94244, d124029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94244, d124029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94245 q = 1) (hb : d122306 q = 1) : d124030 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94245, d124030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94245, d124030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d94246 q = 1) (hb : d122306 q = 1) : d124031 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94246, d124031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94246, d124031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94252 q = 1) (hb : d122306 q = 1) : d124057 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94252, d124057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94252, d124057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21867 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d122306 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d94253 q = 1) (hb : d122306 q = 1) : d124058 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94253, d124058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94253, d124058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d94254 q = 1) (hb : d122306 q = 1) : d124059 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94254, d124059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94254, d124059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94255 q = 1) (hb : d122306 q = 1) : d124060 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94255, d124060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94255, d124060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94256 q = 1) (hb : d122306 q = 1) : d124061 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94256, d124061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94256, d124061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d94257 q = 1) (hb : d122306 q = 1) : d124062 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94257, d124062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94257, d124062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro21869 (p : Pattern) (ha : d94263 p = 1) (hb : d122306 p = 1) : d124068 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d122306 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d94220 q = 1) (hb : d122306 q = 1) : d123942 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94220, d123942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94220, d123942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21846 q ha hb
  have h3 (q : Pattern) (ha : d94221 q = 1) (hb : d122306 q = 1) : d123943 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94221, d123943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94221, d123943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94222 q = 1) (hb : d122306 q = 1) : d123944 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94222, d123944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94222, d123944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94223 q = 1) (hb : d122306 q = 1) : d123945 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94223, d123945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94223, d123945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94224 q = 1) (hb : d122306 q = 1) : d123946 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94224, d123946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94224, d123946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94258 q = 1) (hb : d122306 q = 1) : d124063 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94258, d124063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94258, d124063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21868 q ha hb
  have h8 (q : Pattern) (ha : d94259 q = 1) (hb : d122306 q = 1) : d124064 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94259, d124064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94259, d124064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94260 q = 1) (hb : d122306 q = 1) : d124065 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94260, d124065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94260, d124065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94261 q = 1) (hb : d122306 q = 1) : d124066 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94261, d124066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94261, d124066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94262 q = 1) (hb : d122306 q = 1) : d124067 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94262, d124067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94262, d124067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d94263 q = 1) (hb : d122306 q = 1) : d124068 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94263, d124068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94263, d124068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro21870 (p : Pattern) (ha : d481 p = 1) (hb : d122306 p = 1) : d124070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d122305 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d122305 q = 1) : d123880 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21835 q ha hb
    | true =>
      simp only [d145, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d122305 q = 1) : d123881 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d122305 q = 1) : d123882 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d475 q = 1) (hb : d122306 q = 1) : d123883 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d122306, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d475, d122306, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d480 q = 1) (hb : d122306 q = 1) : d124069 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d124069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d480, d124069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d481 q = 1) (hb : d122306 q = 1) : d124070 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d124070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d481, d124070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h9 p ha hb
theorem andIntro21871 (p : Pattern) (ha : d491 p = 1) (hb : d122306 p = 1) : d124080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21870 q ha hb
    | true =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d122306 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d122306 q = 1) : d124078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d122306 q = 1) : d124079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d122306 q = 1) : d124080 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d124080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d124080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21872 (p : Pattern) (ha : d501 p = 1) (hb : d122306 p = 1) : d124090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21870 q ha hb
    | true =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d122306 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d122306 q = 1) : d124078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d122306 q = 1) : d124079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d122306 q = 1) : d124090 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d124090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d124090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21873 (p : Pattern) (ha : d644 p = 1) (hb : d122306 p = 1) : d124175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d122306 q = 1) : d124164 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21871 q ha hb
    | true =>
      simp only [d633, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d122306 q = 1) : d124165 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d122306 q = 1) : d124166 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d122306 q = 1) : d124167 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d122306 q = 1) : d124168 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d639 q = 1) (hb : d122306 q = 1) : d124170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21872 q ha hb
    | true =>
      simp only [d639, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d640 q = 1) (hb : d122306 q = 1) : d124171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d641 q = 1) (hb : d122306 q = 1) : d124172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d641, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d642 q = 1) (hb : d122306 q = 1) : d124173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d643 q = 1) (hb : d122306 q = 1) : d124174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d644 q = 1) (hb : d122306 q = 1) : d124175 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, d124175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d644, d124175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21874 (p : Pattern) (ha : d653 p = 1) (hb : d122306 p = 1) : d124184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d122306 q = 1) : d124170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21872 q ha hb
    | true =>
      simp only [d639, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d122306 q = 1) : d124171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d122306 q = 1) : d124172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d122306 q = 1) : d124173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d122306 q = 1) : d124174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d122306 q = 1) : d124184 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, d124184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, d124184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21875 (p : Pattern) (ha : d683 p = 1) (hb : d122306 p = 1) : d124204 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d122305 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d122305 q = 1) : d123918 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21842 q ha hb
    | true =>
      simp only [d232, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d122305 q = 1) : d123919 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d122305 q = 1) : d123920 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d673 q = 1) (hb : d122306 q = 1) : d123921 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d122306, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d673, d122306, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d682 q = 1) (hb : d122306 q = 1) : d124203 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d124203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d682, d124203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d683 q = 1) (hb : d122306 q = 1) : d124204 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d124204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d683, d124204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h9 p ha hb
theorem andIntro21876 (p : Pattern) (ha : d730 p = 1) (hb : d122306 p = 1) : d124227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d122306 q = 1) : d124205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21875 q ha hb
    | true =>
      simp only [d684, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d122306 q = 1) : d124206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d122306 q = 1) : d124224 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d124224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d124224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d122306 q = 1) : d124225 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d124225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d124225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d122306 q = 1) : d124226 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d124226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d124226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d122306 q = 1) : d124227 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d124227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d124227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21877 (p : Pattern) (ha : d736 p = 1) (hb : d122306 p = 1) : d124233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d122306 q = 1) : d124228 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d124228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21876 q ha hb
    | true =>
      simp only [d731, d124228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d122306 q = 1) : d124229 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d124229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, d124229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d122306 q = 1) : d124230 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d124230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, d124230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d122306 q = 1) : d124231 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, d124231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, d124231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d122306 q = 1) : d124232 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, d124232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, d124232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d122306 q = 1) : d124233 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, d124233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, d124233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21878 (p : Pattern) (ha : d8420 p = 1) (hb : d122306 p = 1) : d124076 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21853 q ha hb
    | true =>
      simp only [d8314, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21870 q ha hb
    | true =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d122306 q = 1) : d124073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8418 q = 1) (hb : d122306 q = 1) : d124074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8418, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8419 q = 1) (hb : d122306 q = 1) : d124075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8419, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8419, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8420 q = 1) (hb : d122306 q = 1) : d124076 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8420, d124076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8420, d124076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21879 (p : Pattern) (ha : d8426 p = 1) (hb : d122306 p = 1) : d124086 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8421 q = 1) (hb : d122306 q = 1) : d124081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8421, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21878 q ha hb
    | true =>
      simp only [d8421, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21871 q ha hb
  have h2 (q : Pattern) (ha : d8422 q = 1) (hb : d122306 q = 1) : d124082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8422, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8422, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8423 q = 1) (hb : d122306 q = 1) : d124083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8423, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8423, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8424 q = 1) (hb : d122306 q = 1) : d124084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8424, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8424, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8425 q = 1) (hb : d122306 q = 1) : d124085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8425, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8425, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8426 q = 1) (hb : d122306 q = 1) : d124086 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8426, d124086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8426, d124086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21880 (p : Pattern) (ha : d8429 p = 1) (hb : d122306 p = 1) : d124089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21853 q ha hb
    | true =>
      simp only [d8314, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21870 q ha hb
    | true =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d122306 q = 1) : d124073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8418 q = 1) (hb : d122306 q = 1) : d124074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8418, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8419 q = 1) (hb : d122306 q = 1) : d124075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8419, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8419, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8429 q = 1) (hb : d122306 q = 1) : d124089 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8429, d124089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8429, d124089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro21881 (p : Pattern) (ha : d8435 p = 1) (hb : d122306 p = 1) : d124096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8421 q = 1) (hb : d122306 q = 1) : d124081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8421, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21878 q ha hb
    | true =>
      simp only [d8421, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21871 q ha hb
  have h2 (q : Pattern) (ha : d8422 q = 1) (hb : d122306 q = 1) : d124082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8422, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8422, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8423 q = 1) (hb : d122306 q = 1) : d124083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8423, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8423, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8424 q = 1) (hb : d122306 q = 1) : d124084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8424, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8424, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8425 q = 1) (hb : d122306 q = 1) : d124085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8425, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8425, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8430 q = 1) (hb : d122306 q = 1) : d124091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8430, d124091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21880 q ha hb
    | true =>
      simp only [d8430, d124091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21872 q ha hb
  have h7 (q : Pattern) (ha : d8431 q = 1) (hb : d122306 q = 1) : d124092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8431, d124092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8431, d124092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8432 q = 1) (hb : d122306 q = 1) : d124093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8432, d124093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8432, d124093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8433 q = 1) (hb : d122306 q = 1) : d124094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8433, d124094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8433, d124094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8434 q = 1) (hb : d122306 q = 1) : d124095 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8434, d124095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8434, d124095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8435 q = 1) (hb : d122306 q = 1) : d124096 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8435, d124096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8435, d124096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21882 (p : Pattern) (ha : d4818 p = 1) (hb : d122305 p = 1) : d123879 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d142 q = 1) : d142 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d143 q = 1) (hb : d122304 q = 1) : d13980 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d122304, d13980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d143, d122304, d13980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4818 q = 1) (hb : d122305 q = 1) : d123879 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d4818, d122305, d123879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4818, d122305, d123879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro21883 (p : Pattern) (ha : d6799 p = 1) (hb : d122306 p = 1) : d123980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325 q = 1) (hb : d122305 q = 1) : d123975 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21852 q ha hb
    | true =>
      simp only [d325, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21835 q ha hb
  have h2 (q : Pattern) (ha : d326 q = 1) (hb : d122305 q = 1) : d123976 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d327 q = 1) (hb : d122305 q = 1) : d123977 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6797 q = 1) (hb : d122306 q = 1) : d123978 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6797, d122306, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6797, d122306, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30 q = 1) (hb : d122305 q = 1) : d30 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4819 q = 1) (hb : d122305 q = 1) : d123880 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21882 q ha hb
    | true =>
      simp only [d4819, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4820 q = 1) (hb : d122305 q = 1) : d123881 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4821 q = 1) (hb : d122305 q = 1) : d123882 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4822 q = 1) (hb : d122306 q = 1) : d123883 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d122306, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4822, d122306, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d6798 q = 1) (hb : d122306 q = 1) : d123979 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6798, d123979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6798, d123979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d6799 q = 1) (hb : d122306 q = 1) : d123980 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6799, d123980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6799, d123980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro21884 (p : Pattern) (ha : d8463 p = 1) (hb : d122306 p = 1) : d124076 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6800 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21883 q ha hb
    | true =>
      simp only [d6800, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6801 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21870 q ha hb
    | true =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8460 q = 1) (hb : d122306 q = 1) : d124073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8460, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8460, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8461 q = 1) (hb : d122306 q = 1) : d124074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8461, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8461, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8462 q = 1) (hb : d122306 q = 1) : d124075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8462, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8462, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8463 q = 1) (hb : d122306 q = 1) : d124076 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8463, d124076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8463, d124076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21885 (p : Pattern) (ha : d8514 p = 1) (hb : d122306 p = 1) : d124169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8509 q = 1) (hb : d122306 q = 1) : d124081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8509, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21884 q ha hb
    | true =>
      simp only [d8509, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21871 q ha hb
  have h2 (q : Pattern) (ha : d8510 q = 1) (hb : d122306 q = 1) : d124082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8510, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8510, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8511 q = 1) (hb : d122306 q = 1) : d124083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8511, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8511, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8512 q = 1) (hb : d122306 q = 1) : d124084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8512, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8512, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8513 q = 1) (hb : d122306 q = 1) : d124085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8513, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8513, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d122306 q = 1) : d124164 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21871 q ha hb
    | true =>
      simp only [d633, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d122306 q = 1) : d124165 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d122306 q = 1) : d124166 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d122306 q = 1) : d124167 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d122306 q = 1) : d124168 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8514 q = 1) (hb : d122306 q = 1) : d124169 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8514, d124169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8514, d124169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21886 (p : Pattern) (ha : d514 p = 1) (hb : d122306 p = 1) : d124103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21870 q ha hb
    | true =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d122306 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d122306 q = 1) : d124078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d122306 q = 1) : d124102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d514 q = 1) (hb : d122306 q = 1) : d124103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, d124103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, d124103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21887 (p : Pattern) (ha : d524 p = 1) (hb : d122306 p = 1) : d124113 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21870 q ha hb
    | true =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d122306 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d122306 q = 1) : d124111 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d122306 q = 1) : d124112 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d122306 q = 1) : d124113 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, d124113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, d124113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21888 (p : Pattern) (ha : d8440 p = 1) (hb : d122306 p = 1) : d124101 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21853 q ha hb
    | true =>
      simp only [d8314, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21870 q ha hb
    | true =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d122306 q = 1) : d124073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8418 q = 1) (hb : d122306 q = 1) : d124074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8418, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8439 q = 1) (hb : d122306 q = 1) : d124100 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8439, d124100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8439, d124100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8440 q = 1) (hb : d122306 q = 1) : d124101 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8440, d124101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8440, d124101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21889 (p : Pattern) (ha : d8447 p = 1) (hb : d122306 p = 1) : d124110 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21853 q ha hb
    | true =>
      simp only [d8314, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21870 q ha hb
    | true =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d122306 q = 1) : d124073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8445 q = 1) (hb : d122306 q = 1) : d124108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8445, d124108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8445, d124108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8446 q = 1) (hb : d122306 q = 1) : d124109 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8446, d124109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8446, d124109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8447 q = 1) (hb : d122306 q = 1) : d124110 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8447, d124110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8447, d124110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21890 (p : Pattern) (ha : d548 p = 1) (hb : d122305 p = 1) : d124117 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d546 q = 1) : d546 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d322 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d547 q = 1) (hb : d122304 q = 1) : d14261 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d547, d122304, d14261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d547, d122304, d14261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d323 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d548 q = 1) (hb : d122305 q = 1) : d124117 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d548, d122305, d124117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d548, d122305, d124117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro21891 (p : Pattern) (ha : d8453 p = 1) (hb : d122306 p = 1) : d124123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d549 q = 1) (hb : d122305 q = 1) : d124118 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d549, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21890 q ha hb
    | true =>
      simp only [d549, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21852 q ha hb
  have h2 (q : Pattern) (ha : d550 q = 1) (hb : d122305 q = 1) : d124119 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d550, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d550, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d551 q = 1) (hb : d122305 q = 1) : d124120 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d551, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d551, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8451 q = 1) (hb : d122306 q = 1) : d124121 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8451, d122306, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8451, d122306, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d325 q = 1) (hb : d122305 q = 1) : d123975 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21852 q ha hb
    | true =>
      simp only [d325, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21835 q ha hb
  have h7 (q : Pattern) (ha : d326 q = 1) (hb : d122305 q = 1) : d123976 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d327 q = 1) (hb : d122305 q = 1) : d123977 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6797 q = 1) (hb : d122306 q = 1) : d123978 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6797, d122306, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6797, d122306, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8452 q = 1) (hb : d122306 q = 1) : d124122 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8452, d124122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8452, d124122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8453 q = 1) (hb : d122306 q = 1) : d124123 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8453, d124123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8453, d124123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro21892 (p : Pattern) (ha : d8459 p = 1) (hb : d122306 p = 1) : d124129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8454 q = 1) (hb : d122306 q = 1) : d124124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8454, d124124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21891 q ha hb
    | true =>
      simp only [d8454, d124124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8455 q = 1) (hb : d122306 q = 1) : d124125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8455, d124125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8455, d124125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6800 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21883 q ha hb
    | true =>
      simp only [d6800, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6801 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8456 q = 1) (hb : d122306 q = 1) : d124126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8456, d124126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8456, d124126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8457 q = 1) (hb : d122306 q = 1) : d124127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8457, d124127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8457, d124127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8458 q = 1) (hb : d122306 q = 1) : d124128 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8458, d124128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8458, d124128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8459 q = 1) (hb : d122306 q = 1) : d124129 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8459, d124129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8459, d124129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21893 (p : Pattern) (ha : d8479 p = 1) (hb : d122306 p = 1) : d124135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21853 q ha hb
    | true =>
      simp only [d8314, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8476 q = 1) (hb : d122306 q = 1) : d124132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d124132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d124132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8477 q = 1) (hb : d122306 q = 1) : d124133 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, d124133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8477, d124133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8478 q = 1) (hb : d122306 q = 1) : d124134 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8478, d124134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8478, d124134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8479 q = 1) (hb : d122306 q = 1) : d124135 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8479, d124135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8479, d124135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21894 (p : Pattern) (ha : d94268 p = 1) (hb : d122306 p = 1) : d124141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8441 q = 1) (hb : d122306 q = 1) : d124104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8441, d124104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21888 q ha hb
    | true =>
      simp only [d8441, d124104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21886 q ha hb
  have h2 (q : Pattern) (ha : d8442 q = 1) (hb : d122306 q = 1) : d124105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8442, d124105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8442, d124105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8443 q = 1) (hb : d122306 q = 1) : d124106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8443, d124106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8443, d124106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8444 q = 1) (hb : d122306 q = 1) : d124107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8444, d124107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8444, d124107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8448 q = 1) (hb : d122306 q = 1) : d124114 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8448, d124114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21889 q ha hb
    | true =>
      simp only [d8448, d124114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21887 q ha hb
  have h6 (q : Pattern) (ha : d8449 q = 1) (hb : d122306 q = 1) : d124115 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8449, d124115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8449, d124115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8450 q = 1) (hb : d122306 q = 1) : d124116 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8450, d124116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8450, d124116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8464 q = 1) (hb : d122306 q = 1) : d124130 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8464, d124130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21892 q ha hb
    | true =>
      simp only [d8464, d124130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21884 q ha hb
  have h9 (q : Pattern) (ha : d94264 q = 1) (hb : d122306 q = 1) : d124131 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94264, d124131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94264, d124131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8480 q = 1) (hb : d122306 q = 1) : d124136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8480, d124136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21893 q ha hb
    | true =>
      simp only [d8480, d124136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8481 q = 1) (hb : d122306 q = 1) : d124137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8481, d124137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8481, d124137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94265 q = 1) (hb : d122306 q = 1) : d124138 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94265, d124138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94265, d124138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94266 q = 1) (hb : d122306 q = 1) : d124139 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94266, d124139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94266, d124139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94267 q = 1) (hb : d122306 q = 1) : d124140 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94267, d124140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94267, d124140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94268 q = 1) (hb : d122306 q = 1) : d124141 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94268, d124141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94268, d124141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro21895 (p : Pattern) (ha : d610 p = 1) (hb : d122306 p = 1) : d124143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21870 q ha hb
    | true =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d122306 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d122306 q = 1) : d124078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d122306 q = 1) : d124102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d610 q = 1) (hb : d122306 q = 1) : d124143 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, d124143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d610, d124143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21896 (p : Pattern) (ha : d616 p = 1) (hb : d122306 p = 1) : d124149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21870 q ha hb
    | true =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d122306 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d122306 q = 1) : d124111 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d122306 q = 1) : d124112 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d616 q = 1) (hb : d122306 q = 1) : d124149 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, d124149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d616, d124149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21897 (p : Pattern) (ha : d8486 p = 1) (hb : d122306 p = 1) : d124142 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21853 q ha hb
    | true =>
      simp only [d8314, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21870 q ha hb
    | true =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d122306 q = 1) : d124073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8418 q = 1) (hb : d122306 q = 1) : d124074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8418, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8439 q = 1) (hb : d122306 q = 1) : d124100 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8439, d124100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8439, d124100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8486 q = 1) (hb : d122306 q = 1) : d124142 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8486, d124142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8486, d124142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro21898 (p : Pattern) (ha : d8491 p = 1) (hb : d122306 p = 1) : d124148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21853 q ha hb
    | true =>
      simp only [d8314, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21870 q ha hb
    | true =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d122306 q = 1) : d124073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8445 q = 1) (hb : d122306 q = 1) : d124108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8445, d124108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8445, d124108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8446 q = 1) (hb : d122306 q = 1) : d124109 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8446, d124109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8446, d124109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8491 q = 1) (hb : d122306 q = 1) : d124148 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8491, d124148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8491, d124148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro21899 (p : Pattern) (ha : d8495 p = 1) (hb : d122306 p = 1) : d124153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8454 q = 1) (hb : d122306 q = 1) : d124124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8454, d124124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21891 q ha hb
    | true =>
      simp only [d8454, d124124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8455 q = 1) (hb : d122306 q = 1) : d124125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8455, d124125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8455, d124125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6800 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21883 q ha hb
    | true =>
      simp only [d6800, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6801 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8456 q = 1) (hb : d122306 q = 1) : d124126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8456, d124126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8456, d124126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8457 q = 1) (hb : d122306 q = 1) : d124127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8457, d124127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8457, d124127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8458 q = 1) (hb : d122306 q = 1) : d124128 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8458, d124128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8458, d124128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8495 q = 1) (hb : d122306 q = 1) : d124153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8495, d124153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8495, d124153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro21900 (p : Pattern) (ha : d8496 p = 1) (hb : d122306 p = 1) : d124089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6800 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21883 q ha hb
    | true =>
      simp only [d6800, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6801 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21870 q ha hb
    | true =>
      simp only [d482, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8460 q = 1) (hb : d122306 q = 1) : d124073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8460, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8460, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8461 q = 1) (hb : d122306 q = 1) : d124074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8461, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8461, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8462 q = 1) (hb : d122306 q = 1) : d124075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8462, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8462, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8496 q = 1) (hb : d122306 q = 1) : d124089 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8496, d124089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8496, d124089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro21901 (p : Pattern) (ha : d8501 p = 1) (hb : d122306 p = 1) : d124156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21853 q ha hb
    | true =>
      simp only [d8314, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8476 q = 1) (hb : d122306 q = 1) : d124132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8476, d124132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8476, d124132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8477 q = 1) (hb : d122306 q = 1) : d124133 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8477, d124133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8477, d124133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8478 q = 1) (hb : d122306 q = 1) : d124134 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8478, d124134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8478, d124134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8501 q = 1) (hb : d122306 q = 1) : d124156 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8501, d124156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8501, d124156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21902 (p : Pattern) (ha : d94273 p = 1) (hb : d122306 p = 1) : d124162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8441 q = 1) (hb : d122306 q = 1) : d124104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8441, d124104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21888 q ha hb
    | true =>
      simp only [d8441, d124104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21886 q ha hb
  have h2 (q : Pattern) (ha : d8442 q = 1) (hb : d122306 q = 1) : d124105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8442, d124105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8442, d124105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8443 q = 1) (hb : d122306 q = 1) : d124106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8443, d124106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8443, d124106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8444 q = 1) (hb : d122306 q = 1) : d124107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8444, d124107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8444, d124107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8448 q = 1) (hb : d122306 q = 1) : d124114 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8448, d124114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21889 q ha hb
    | true =>
      simp only [d8448, d124114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21887 q ha hb
  have h6 (q : Pattern) (ha : d8449 q = 1) (hb : d122306 q = 1) : d124115 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8449, d124115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8449, d124115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8450 q = 1) (hb : d122306 q = 1) : d124116 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8450, d124116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8450, d124116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8464 q = 1) (hb : d122306 q = 1) : d124130 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8464, d124130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21892 q ha hb
    | true =>
      simp only [d8464, d124130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21884 q ha hb
  have h9 (q : Pattern) (ha : d94264 q = 1) (hb : d122306 q = 1) : d124131 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94264, d124131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94264, d124131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8480 q = 1) (hb : d122306 q = 1) : d124136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8480, d124136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21893 q ha hb
    | true =>
      simp only [d8480, d124136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8481 q = 1) (hb : d122306 q = 1) : d124137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8481, d124137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8481, d124137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94265 q = 1) (hb : d122306 q = 1) : d124138 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94265, d124138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94265, d124138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94266 q = 1) (hb : d122306 q = 1) : d124139 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94266, d124139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94266, d124139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94267 q = 1) (hb : d122306 q = 1) : d124140 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94267, d124140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94267, d124140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8487 q = 1) (hb : d122306 q = 1) : d124144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8487, d124144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21897 q ha hb
    | true =>
      simp only [d8487, d124144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21895 q ha hb
  have h16 (q : Pattern) (ha : d8488 q = 1) (hb : d122306 q = 1) : d124145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8488, d124145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8488, d124145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8489 q = 1) (hb : d122306 q = 1) : d124146 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8489, d124146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d8489, d124146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d8490 q = 1) (hb : d122306 q = 1) : d124147 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8490, d124147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8490, d124147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8492 q = 1) (hb : d122306 q = 1) : d124150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8492, d124150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21898 q ha hb
    | true =>
      simp only [d8492, d124150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21896 q ha hb
  have h20 (q : Pattern) (ha : d8493 q = 1) (hb : d122306 q = 1) : d124151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8493, d124151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8493, d124151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d8494 q = 1) (hb : d122306 q = 1) : d124152 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8494, d124152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d8494, d124152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8497 q = 1) (hb : d122306 q = 1) : d124154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8497, d124154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21899 q ha hb
    | true =>
      simp only [d8497, d124154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21900 q ha hb
  have h23 (q : Pattern) (ha : d94269 q = 1) (hb : d122306 q = 1) : d124155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94269, d124155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94269, d124155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d8502 q = 1) (hb : d122306 q = 1) : d124157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8502, d124157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21901 q ha hb
    | true =>
      simp only [d8502, d124157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8503 q = 1) (hb : d122306 q = 1) : d124158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8503, d124158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8503, d124158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94270 q = 1) (hb : d122306 q = 1) : d124159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94270, d124159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94270, d124159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94271 q = 1) (hb : d122306 q = 1) : d124160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94271, d124160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94271, d124160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94272 q = 1) (hb : d122306 q = 1) : d124161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94272, d124161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94272, d124161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94273 q = 1) (hb : d122306 q = 1) : d124162 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94273, d124162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94273, d124162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro21903 (p : Pattern) (ha : d94280 p = 1) (hb : d122306 p = 1) : d124182 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8497 q = 1) (hb : d122306 q = 1) : d124154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8497, d124154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21899 q ha hb
    | true =>
      simp only [d8497, d124154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21900 q ha hb
  have h2 (q : Pattern) (ha : d94269 q = 1) (hb : d122306 q = 1) : d124155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94269, d124155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94269, d124155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8502 q = 1) (hb : d122306 q = 1) : d124157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8502, d124157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21901 q ha hb
    | true =>
      simp only [d8502, d124157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8503 q = 1) (hb : d122306 q = 1) : d124158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8503, d124158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8503, d124158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94270 q = 1) (hb : d122306 q = 1) : d124159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94270, d124159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94270, d124159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94278 q = 1) (hb : d122306 q = 1) : d124180 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94278, d124180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94278, d124180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94279 q = 1) (hb : d122306 q = 1) : d124181 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94279, d124181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94279, d124181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94280 q = 1) (hb : d122306 q = 1) : d124182 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94280, d124182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94280, d124182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21904 (p : Pattern) (ha : d6078 p = 1) (hb : d122305 p = 1) : d123917 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d229 q = 1) : d229 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d230 q = 1) (hb : d122304 q = 1) : d14019 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d122304, d14019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d230, d122304, d14019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6078 q = 1) (hb : d122305 q = 1) : d123917 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6078, d122305, d123917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6078, d122305, d123917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro21905 (p : Pattern) (ha : d6845 p = 1) (hb : d122306 p = 1) : d124038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d418 q = 1) (hb : d122305 q = 1) : d124033 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21863 q ha hb
    | true =>
      simp only [d418, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21842 q ha hb
  have h2 (q : Pattern) (ha : d419 q = 1) (hb : d122305 q = 1) : d124034 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d420 q = 1) (hb : d122305 q = 1) : d124035 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6843 q = 1) (hb : d122306 q = 1) : d124036 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6843, d122306, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6843, d122306, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71 q = 1) (hb : d122305 q = 1) : d71 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6079 q = 1) (hb : d122305 q = 1) : d123918 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21904 q ha hb
    | true =>
      simp only [d6079, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6080 q = 1) (hb : d122305 q = 1) : d123919 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6081 q = 1) (hb : d122305 q = 1) : d123920 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6082 q = 1) (hb : d122306 q = 1) : d123921 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d122306, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6082, d122306, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d6844 q = 1) (hb : d122306 q = 1) : d124037 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6844, d124037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6844, d124037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d6845 q = 1) (hb : d122306 q = 1) : d124038 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6845, d124038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6845, d124038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro21906 (p : Pattern) (ha : d664 p = 1) (hb : d122305 p = 1) : d124190 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d662 q = 1) : d662 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d415 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d663 q = 1) (hb : d122304 q = 1) : d14370 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d663, d122304, d14370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d663, d122304, d14370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d416 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d664 q = 1) (hb : d122305 q = 1) : d124190 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d664, d122305, d124190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d664, d122305, d124190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro21907 (p : Pattern) (ha : d8529 p = 1) (hb : d122306 p = 1) : d124196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d665 q = 1) (hb : d122305 q = 1) : d124191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d665, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21906 q ha hb
    | true =>
      simp only [d665, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21863 q ha hb
  have h2 (q : Pattern) (ha : d666 q = 1) (hb : d122305 q = 1) : d124192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d666, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d666, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d667 q = 1) (hb : d122305 q = 1) : d124193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d667, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d667, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8527 q = 1) (hb : d122306 q = 1) : d124194 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8527, d122306, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8527, d122306, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d418 q = 1) (hb : d122305 q = 1) : d124033 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21863 q ha hb
    | true =>
      simp only [d418, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21842 q ha hb
  have h7 (q : Pattern) (ha : d419 q = 1) (hb : d122305 q = 1) : d124034 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d420 q = 1) (hb : d122305 q = 1) : d124035 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6843 q = 1) (hb : d122306 q = 1) : d124036 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6843, d122306, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6843, d122306, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8528 q = 1) (hb : d122306 q = 1) : d124195 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8528, d124195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8528, d124195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8529 q = 1) (hb : d122306 q = 1) : d124196 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8529, d124196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8529, d124196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro21908 (p : Pattern) (ha : d8535 p = 1) (hb : d122306 p = 1) : d124202 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8530 q = 1) (hb : d122306 q = 1) : d124197 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8530, d124197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21907 q ha hb
    | true =>
      simp only [d8530, d124197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8531 q = 1) (hb : d122306 q = 1) : d124198 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8531, d124198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8531, d124198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6846 q = 1) (hb : d122306 q = 1) : d124039 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6846, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21905 q ha hb
    | true =>
      simp only [d6846, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6847 q = 1) (hb : d122306 q = 1) : d124040 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6847, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6847, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8532 q = 1) (hb : d122306 q = 1) : d124199 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8532, d124199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8532, d124199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8533 q = 1) (hb : d122306 q = 1) : d124200 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8533, d124200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8533, d124200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8534 q = 1) (hb : d122306 q = 1) : d124201 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8534, d124201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8534, d124201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8535 q = 1) (hb : d122306 q = 1) : d124202 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8535, d124202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8535, d124202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro21909 (p : Pattern) (ha : d8539 p = 1) (hb : d122306 p = 1) : d124210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6846 q = 1) (hb : d122306 q = 1) : d124039 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6846, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21905 q ha hb
    | true =>
      simp only [d6846, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6847 q = 1) (hb : d122306 q = 1) : d124040 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6847, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6847, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d122306 q = 1) : d124205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21875 q ha hb
    | true =>
      simp only [d684, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d122306 q = 1) : d124206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8536 q = 1) (hb : d122306 q = 1) : d124207 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8536, d124207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8536, d124207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8537 q = 1) (hb : d122306 q = 1) : d124208 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8537, d124208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8537, d124208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8538 q = 1) (hb : d122306 q = 1) : d124209 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8538, d124209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8538, d124209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8539 q = 1) (hb : d122306 q = 1) : d124210 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8539, d124210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8539, d124210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro21910 (p : Pattern) (ha : d8555 p = 1) (hb : d122306 p = 1) : d124216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8378 q = 1) (hb : d122306 q = 1) : d124039 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8378, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21864 q ha hb
    | true =>
      simp only [d8378, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8379 q = 1) (hb : d122306 q = 1) : d124040 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8379, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8379, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8552 q = 1) (hb : d122306 q = 1) : d124213 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8552, d124213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8552, d124213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8553 q = 1) (hb : d122306 q = 1) : d124214 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8553, d124214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8553, d124214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8554 q = 1) (hb : d122306 q = 1) : d124215 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8554, d124215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8554, d124215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8555 q = 1) (hb : d122306 q = 1) : d124216 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8555, d124216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8555, d124216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21911 (p : Pattern) (ha : d94290 p = 1) (hb : d122306 p = 1) : d124222 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8540 q = 1) (hb : d122306 q = 1) : d124211 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8540, d124211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21908 q ha hb
    | true =>
      simp only [d8540, d124211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21909 q ha hb
  have h2 (q : Pattern) (ha : d94286 q = 1) (hb : d122306 q = 1) : d124212 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94286, d124212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94286, d124212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8556 q = 1) (hb : d122306 q = 1) : d124217 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8556, d124217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21910 q ha hb
    | true =>
      simp only [d8556, d124217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8557 q = 1) (hb : d122306 q = 1) : d124218 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8557, d124218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8557, d124218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94287 q = 1) (hb : d122306 q = 1) : d124219 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94287, d124219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94287, d124219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94288 q = 1) (hb : d122306 q = 1) : d124220 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94288, d124220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94288, d124220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94289 q = 1) (hb : d122306 q = 1) : d124221 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94289, d124221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94289, d124221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94290 q = 1) (hb : d122306 q = 1) : d124222 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94290, d124222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94290, d124222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21912 (p : Pattern) (ha : d94296 p = 1) (hb : d122306 p = 1) : d124239 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8427 q = 1) (hb : d122306 q = 1) : d124087 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8427, d124087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8427, d124087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21879 q ha hb
  have h2 (q : Pattern) (ha : d8428 q = 1) (hb : d122306 q = 1) : d124088 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8428, d124088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8428, d124088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8436 q = 1) (hb : d122306 q = 1) : d124097 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8436, d124097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21879 q ha hb
    | true =>
      simp only [d8436, d124097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21881 q ha hb
  have h4 (q : Pattern) (ha : d8437 q = 1) (hb : d122306 q = 1) : d124098 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8437, d124098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8437, d124098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8438 q = 1) (hb : d122306 q = 1) : d124099 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8438, d124099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8438, d124099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94274 q = 1) (hb : d122306 q = 1) : d124163 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94274, d124163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21894 q ha hb
    | true =>
      simp only [d94274, d124163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21902 q ha hb
  have h7 (q : Pattern) (ha : d8515 q = 1) (hb : d122306 q = 1) : d124176 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8515, d124176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21885 q ha hb
    | true =>
      simp only [d8515, d124176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21873 q ha hb
  have h8 (q : Pattern) (ha : d94275 q = 1) (hb : d122306 q = 1) : d124177 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94275, d124177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94275, d124177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94276 q = 1) (hb : d122306 q = 1) : d124178 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94276, d124178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94276, d124178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94277 q = 1) (hb : d122306 q = 1) : d124179 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94277, d124179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94277, d124179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94281 q = 1) (hb : d122306 q = 1) : d124183 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94281, d124183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94281, d124183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21903 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d122306 q = 1) : d124185 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d124185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d124185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21874 q ha hb
  have h13 (q : Pattern) (ha : d94282 q = 1) (hb : d122306 q = 1) : d124186 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94282, d124186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94282, d124186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94283 q = 1) (hb : d122306 q = 1) : d124187 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94283, d124187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94283, d124187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94284 q = 1) (hb : d122306 q = 1) : d124188 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94284, d124188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94284, d124188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94285 q = 1) (hb : d122306 q = 1) : d124189 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94285, d124189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94285, d124189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94291 q = 1) (hb : d122306 q = 1) : d124223 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94291, d124223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94291, d124223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21911 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d122306 q = 1) : d124234 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d124234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d124234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21877 q ha hb
  have h19 (q : Pattern) (ha : d94292 q = 1) (hb : d122306 q = 1) : d124235 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94292, d124235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94292, d124235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d94293 q = 1) (hb : d122306 q = 1) : d124236 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94293, d124236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94293, d124236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94294 q = 1) (hb : d122306 q = 1) : d124237 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94294, d124237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94294, d124237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94295 q = 1) (hb : d122306 q = 1) : d124238 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94295, d124238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94295, d124238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94296 q = 1) (hb : d122306 q = 1) : d124239 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94296, d124239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94296, d124239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro21913 (p : Pattern) (ha : d94302 p = 1) (hb : d122306 p = 1) : d124245 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94297 q = 1) (hb : d122306 q = 1) : d124240 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94297, d124240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94297, d124240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21912 q ha hb
  have h2 (q : Pattern) (ha : d94298 q = 1) (hb : d122306 q = 1) : d124241 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94298, d124241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94298, d124241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94299 q = 1) (hb : d122306 q = 1) : d124242 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94299, d124242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94299, d124242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94300 q = 1) (hb : d122306 q = 1) : d124243 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94300, d124243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94300, d124243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94301 q = 1) (hb : d122306 q = 1) : d124244 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94301, d124244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94301, d124244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94302 q = 1) (hb : d122306 q = 1) : d124245 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94302, d124245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94302, d124245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21914 (p : Pattern) (ha : d758 p = 1) (hb : d122305 p = 1) : d123974 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d322 q = 1) : d322 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d754 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d755 q = 1) (hb : d122304 q = 1) : d14077 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d122304, d14077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d755, d122304, d14077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d757 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d758 q = 1) (hb : d122305 q = 1) : d123974 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d758, d122305, d123974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d758, d122305, d123974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro21915 (p : Pattern) (ha : d773 p = 1) (hb : d122306 p = 1) : d124256 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d762 q = 1) (hb : d122305 q = 1) : d762 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d763 q = 1) (hb : d122305 q = 1) : d124247 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21914 q ha hb
    | true =>
      simp only [d763, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d764 q = 1) (hb : d122305 q = 1) : d124248 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d765 q = 1) (hb : d122305 q = 1) : d124249 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d767 q = 1) (hb : d122306 q = 1) : d124250 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d122306, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d767, d122306, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d772 q = 1) (hb : d122306 q = 1) : d124255 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, d124255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d772, d124255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d773 q = 1) (hb : d122306 q = 1) : d124256 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d773, d124256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d773, d124256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h9 p ha hb
theorem andIntro21916 (p : Pattern) (ha : d783 p = 1) (hb : d122306 p = 1) : d124266 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21915 q ha hb
    | true =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d122306 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d122306 q = 1) : d124264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d122306 q = 1) : d124265 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d783 q = 1) (hb : d122306 q = 1) : d124266 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, d124266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, d124266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21917 (p : Pattern) (ha : d793 p = 1) (hb : d122306 p = 1) : d124276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21915 q ha hb
    | true =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d122306 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d122306 q = 1) : d124264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d122306 q = 1) : d124265 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d793 q = 1) (hb : d122306 q = 1) : d124276 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, d124276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d793, d124276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21918 (p : Pattern) (ha : d950 p = 1) (hb : d122306 p = 1) : d124361 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d122306 q = 1) : d124350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21916 q ha hb
    | true =>
      simp only [d939, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d122306 q = 1) : d124351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d122306 q = 1) : d124352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d122306 q = 1) : d124353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d122306 q = 1) : d124354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d945 q = 1) (hb : d122306 q = 1) : d124356 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21917 q ha hb
    | true =>
      simp only [d945, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d946 q = 1) (hb : d122306 q = 1) : d124357 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d947 q = 1) (hb : d122306 q = 1) : d124358 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d947, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d948 q = 1) (hb : d122306 q = 1) : d124359 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d949 q = 1) (hb : d122306 q = 1) : d124360 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d950 q = 1) (hb : d122306 q = 1) : d124361 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, d124361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d950, d124361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21919 (p : Pattern) (ha : d959 p = 1) (hb : d122306 p = 1) : d124370 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d945 q = 1) (hb : d122306 q = 1) : d124356 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21917 q ha hb
    | true =>
      simp only [d945, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d946 q = 1) (hb : d122306 q = 1) : d124357 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d122306 q = 1) : d124358 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d947, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d122306 q = 1) : d124359 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d122306 q = 1) : d124360 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d122306 q = 1) : d124370 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, d124370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, d124370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21920 (p : Pattern) (ha : d981 p = 1) (hb : d122305 p = 1) : d124032 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d415 q = 1) : d415 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d975 q = 1) (hb : d122304 q = 1) : d14154 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d122304, d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d975, d122304, d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d980 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d981 q = 1) (hb : d122305 q = 1) : d124032 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d981, d122305, d124032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d981, d122305, d124032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro21921 (p : Pattern) (ha : d1005 p = 1) (hb : d122306 p = 1) : d124398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d986 q = 1) (hb : d122305 q = 1) : d986 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d987 q = 1) (hb : d122305 q = 1) : d124385 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21920 q ha hb
    | true =>
      simp only [d987, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d988 q = 1) (hb : d122305 q = 1) : d124386 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d989 q = 1) (hb : d122305 q = 1) : d124387 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d995 q = 1) (hb : d122306 q = 1) : d124388 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d122306, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d995, d122306, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1004 q = 1) (hb : d122306 q = 1) : d124397 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d124397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1004, d124397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1005 q = 1) (hb : d122306 q = 1) : d124398 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, d124398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1005, d124398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h9 p ha hb
theorem andIntro21922 (p : Pattern) (ha : d1063 p = 1) (hb : d122306 p = 1) : d124421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d122306 q = 1) : d124399 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21921 q ha hb
    | true =>
      simp only [d1006, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d122306 q = 1) : d124400 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1060 q = 1) (hb : d122306 q = 1) : d124418 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d124418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, d124418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d122306 q = 1) : d124419 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, d124419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1061, d124419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d122306 q = 1) : d124420 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, d124420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, d124420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d122306 q = 1) : d124421 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, d124421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, d124421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21923 (p : Pattern) (ha : d1069 p = 1) (hb : d122306 p = 1) : d124427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d122306 q = 1) : d124422 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, d124422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21922 q ha hb
    | true =>
      simp only [d1064, d124422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d122306 q = 1) : d124423 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d124423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, d124423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d122306 q = 1) : d124424 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d124424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, d124424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d122306 q = 1) : d124425 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, d124425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, d124425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d122306 q = 1) : d124426 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, d124426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, d124426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d122306 q = 1) : d124427 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, d124427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, d124427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21924 (p : Pattern) (ha : d756 p = 1) (hb : d122305 p = 1) : d124117 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d546 q = 1) : d546 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d322 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d547 q = 1) (hb : d122304 q = 1) : d14261 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d547, d122304, d14261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d547, d122304, d14261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d756 q = 1) (hb : d122305 q = 1) : d124117 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d756, d122305, d124117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d756, d122305, d124117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro21925 (p : Pattern) (ha : d8576 p = 1) (hb : d122306 p = 1) : d124252 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d759 q = 1) (hb : d122305 q = 1) : d124118 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21924 q ha hb
    | true =>
      simp only [d759, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21914 q ha hb
  have h2 (q : Pattern) (ha : d760 q = 1) (hb : d122305 q = 1) : d124119 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d761 q = 1) (hb : d122305 q = 1) : d124120 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6875 q = 1) (hb : d122306 q = 1) : d124121 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6875, d122306, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6875, d122306, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d762 q = 1) (hb : d122305 q = 1) : d762 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d763 q = 1) (hb : d122305 q = 1) : d124247 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21914 q ha hb
    | true =>
      simp only [d763, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d764 q = 1) (hb : d122305 q = 1) : d124248 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d765 q = 1) (hb : d122305 q = 1) : d124249 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d767 q = 1) (hb : d122306 q = 1) : d124250 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d122306, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d767, d122306, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d8575 q = 1) (hb : d122306 q = 1) : d124251 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8575, d124251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8575, d124251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8576 q = 1) (hb : d122306 q = 1) : d124252 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8576, d124252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8576, d124252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro21926 (p : Pattern) (ha : d8582 p = 1) (hb : d122306 p = 1) : d124262 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21925 q ha hb
    | true =>
      simp only [d8577, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21915 q ha hb
    | true =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8579 q = 1) (hb : d122306 q = 1) : d124259 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8580 q = 1) (hb : d122306 q = 1) : d124260 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8580, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8581 q = 1) (hb : d122306 q = 1) : d124261 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8581, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8581, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8582 q = 1) (hb : d122306 q = 1) : d124262 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8582, d124262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8582, d124262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21927 (p : Pattern) (ha : d8588 p = 1) (hb : d122306 p = 1) : d124272 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8583 q = 1) (hb : d122306 q = 1) : d124267 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8583, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21926 q ha hb
    | true =>
      simp only [d8583, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21916 q ha hb
  have h2 (q : Pattern) (ha : d8584 q = 1) (hb : d122306 q = 1) : d124268 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8584, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8584, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8585 q = 1) (hb : d122306 q = 1) : d124269 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8585, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8585, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8586 q = 1) (hb : d122306 q = 1) : d124270 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8586, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8586, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8587 q = 1) (hb : d122306 q = 1) : d124271 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8587, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8587, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8588 q = 1) (hb : d122306 q = 1) : d124272 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8588, d124272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8588, d124272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21928 (p : Pattern) (ha : d8591 p = 1) (hb : d122306 p = 1) : d124275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21925 q ha hb
    | true =>
      simp only [d8577, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21915 q ha hb
    | true =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8579 q = 1) (hb : d122306 q = 1) : d124259 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8580 q = 1) (hb : d122306 q = 1) : d124260 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8580, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8581 q = 1) (hb : d122306 q = 1) : d124261 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8581, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8581, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8591 q = 1) (hb : d122306 q = 1) : d124275 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8591, d124275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8591, d124275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro21929 (p : Pattern) (ha : d8597 p = 1) (hb : d122306 p = 1) : d124282 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8583 q = 1) (hb : d122306 q = 1) : d124267 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8583, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21926 q ha hb
    | true =>
      simp only [d8583, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21916 q ha hb
  have h2 (q : Pattern) (ha : d8584 q = 1) (hb : d122306 q = 1) : d124268 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8584, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8584, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8585 q = 1) (hb : d122306 q = 1) : d124269 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8585, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8585, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8586 q = 1) (hb : d122306 q = 1) : d124270 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8586, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8586, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8587 q = 1) (hb : d122306 q = 1) : d124271 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8587, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8587, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8592 q = 1) (hb : d122306 q = 1) : d124277 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8592, d124277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21928 q ha hb
    | true =>
      simp only [d8592, d124277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21917 q ha hb
  have h7 (q : Pattern) (ha : d8593 q = 1) (hb : d122306 q = 1) : d124278 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8593, d124278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8593, d124278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8594 q = 1) (hb : d122306 q = 1) : d124279 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8594, d124279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8594, d124279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8595 q = 1) (hb : d122306 q = 1) : d124280 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8595, d124280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8595, d124280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8596 q = 1) (hb : d122306 q = 1) : d124281 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8596, d124281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8596, d124281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8597 q = 1) (hb : d122306 q = 1) : d124282 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8597, d124282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8597, d124282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21930 (p : Pattern) (ha : d4913 p = 1) (hb : d122305 p = 1) : d123974 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d322 q = 1) : d322 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d754 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d755 q = 1) (hb : d122304 q = 1) : d14077 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d122304, d14077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d755, d122304, d14077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4913 q = 1) (hb : d122305 q = 1) : d123974 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d4913, d122305, d123974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4913, d122305, d123974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro21931 (p : Pattern) (ha : d6877 p = 1) (hb : d122306 p = 1) : d124252 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d759 q = 1) (hb : d122305 q = 1) : d124118 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21924 q ha hb
    | true =>
      simp only [d759, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21914 q ha hb
  have h2 (q : Pattern) (ha : d760 q = 1) (hb : d122305 q = 1) : d124119 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d761 q = 1) (hb : d122305 q = 1) : d124120 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6875 q = 1) (hb : d122306 q = 1) : d124121 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6875, d122306, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6875, d122306, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d762 q = 1) (hb : d122305 q = 1) : d762 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4914 q = 1) (hb : d122305 q = 1) : d124247 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21930 q ha hb
    | true =>
      simp only [d4914, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4915 q = 1) (hb : d122305 q = 1) : d124248 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4916 q = 1) (hb : d122305 q = 1) : d124249 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4917 q = 1) (hb : d122306 q = 1) : d124250 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d122306, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4917, d122306, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d6876 q = 1) (hb : d122306 q = 1) : d124251 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6876, d124251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6876, d124251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d6877 q = 1) (hb : d122306 q = 1) : d124252 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6877, d124252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6877, d124252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro21932 (p : Pattern) (ha : d8625 p = 1) (hb : d122306 p = 1) : d124262 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6878 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21931 q ha hb
    | true =>
      simp only [d6878, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6879 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21915 q ha hb
    | true =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8622 q = 1) (hb : d122306 q = 1) : d124259 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8622, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8622, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8623 q = 1) (hb : d122306 q = 1) : d124260 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8623, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8623, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8624 q = 1) (hb : d122306 q = 1) : d124261 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8624, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8624, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8625 q = 1) (hb : d122306 q = 1) : d124262 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8625, d124262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8625, d124262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21933 (p : Pattern) (ha : d8676 p = 1) (hb : d122306 p = 1) : d124355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8671 q = 1) (hb : d122306 q = 1) : d124267 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8671, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21932 q ha hb
    | true =>
      simp only [d8671, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21916 q ha hb
  have h2 (q : Pattern) (ha : d8672 q = 1) (hb : d122306 q = 1) : d124268 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8672, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8672, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8673 q = 1) (hb : d122306 q = 1) : d124269 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8673, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8673, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8674 q = 1) (hb : d122306 q = 1) : d124270 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8674, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8674, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8675 q = 1) (hb : d122306 q = 1) : d124271 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8675, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8675, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d122306 q = 1) : d124350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21916 q ha hb
    | true =>
      simp only [d939, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d122306 q = 1) : d124351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d122306 q = 1) : d124352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d122306 q = 1) : d124353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d122306 q = 1) : d124354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8676 q = 1) (hb : d122306 q = 1) : d124355 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8676, d124355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8676, d124355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21934 (p : Pattern) (ha : d806 p = 1) (hb : d122306 p = 1) : d124289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21915 q ha hb
    | true =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d122306 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d122306 q = 1) : d124264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d122306 q = 1) : d124288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d806 q = 1) (hb : d122306 q = 1) : d124289 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d124289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d124289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21935 (p : Pattern) (ha : d816 p = 1) (hb : d122306 p = 1) : d124299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21915 q ha hb
    | true =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d122306 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d122306 q = 1) : d124297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d122306 q = 1) : d124298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d122306 q = 1) : d124299 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d124299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d124299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21936 (p : Pattern) (ha : d8602 p = 1) (hb : d122306 p = 1) : d124287 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21925 q ha hb
    | true =>
      simp only [d8577, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21915 q ha hb
    | true =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8579 q = 1) (hb : d122306 q = 1) : d124259 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8580 q = 1) (hb : d122306 q = 1) : d124260 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8580, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8601 q = 1) (hb : d122306 q = 1) : d124286 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8601, d124286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8601, d124286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8602 q = 1) (hb : d122306 q = 1) : d124287 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8602, d124287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8602, d124287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21937 (p : Pattern) (ha : d8609 p = 1) (hb : d122306 p = 1) : d124296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21925 q ha hb
    | true =>
      simp only [d8577, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21915 q ha hb
    | true =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8579 q = 1) (hb : d122306 q = 1) : d124259 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8607 q = 1) (hb : d122306 q = 1) : d124294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8607, d124294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8607, d124294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8608 q = 1) (hb : d122306 q = 1) : d124295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8608, d124295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8608, d124295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8609 q = 1) (hb : d122306 q = 1) : d124296 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8609, d124296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8609, d124296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21938 (p : Pattern) (ha : d839 p = 1) (hb : d122305 p = 1) : d124303 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d837 q = 1) : d837 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d546 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d838 q = 1) (hb : d122304 q = 1) : d14528 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d838, d122304, d14528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d838, d122304, d14528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d547 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d839 q = 1) (hb : d122305 q = 1) : d124303 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d839, d122305, d124303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d839, d122305, d124303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro21939 (p : Pattern) (ha : d8615 p = 1) (hb : d122306 p = 1) : d124309 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d840 q = 1) (hb : d122305 q = 1) : d124304 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d840, d124304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21938 q ha hb
    | true =>
      simp only [d840, d124304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21924 q ha hb
  have h2 (q : Pattern) (ha : d841 q = 1) (hb : d122305 q = 1) : d124305 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d841, d124305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d841, d124305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d842 q = 1) (hb : d122305 q = 1) : d124306 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d842, d124306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d842, d124306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8613 q = 1) (hb : d122306 q = 1) : d124307 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8613, d122306, d124307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8613, d122306, d124307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d759 q = 1) (hb : d122305 q = 1) : d124118 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21924 q ha hb
    | true =>
      simp only [d759, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21914 q ha hb
  have h7 (q : Pattern) (ha : d760 q = 1) (hb : d122305 q = 1) : d124119 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d761 q = 1) (hb : d122305 q = 1) : d124120 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6875 q = 1) (hb : d122306 q = 1) : d124121 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6875, d122306, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6875, d122306, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8614 q = 1) (hb : d122306 q = 1) : d124308 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8614, d124308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8614, d124308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8615 q = 1) (hb : d122306 q = 1) : d124309 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8615, d124309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8615, d124309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro21940 (p : Pattern) (ha : d8621 p = 1) (hb : d122306 p = 1) : d124315 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8616 q = 1) (hb : d122306 q = 1) : d124310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8616, d124310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21939 q ha hb
    | true =>
      simp only [d8616, d124310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8617 q = 1) (hb : d122306 q = 1) : d124311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8617, d124311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8617, d124311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6878 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21931 q ha hb
    | true =>
      simp only [d6878, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6879 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8618 q = 1) (hb : d122306 q = 1) : d124312 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8618, d124312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8618, d124312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8619 q = 1) (hb : d122306 q = 1) : d124313 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8619, d124313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8619, d124313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8620 q = 1) (hb : d122306 q = 1) : d124314 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8620, d124314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8620, d124314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8621 q = 1) (hb : d122306 q = 1) : d124315 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8621, d124315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8621, d124315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21941 (p : Pattern) (ha : d8641 p = 1) (hb : d122306 p = 1) : d124321 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21925 q ha hb
    | true =>
      simp only [d8577, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8638 q = 1) (hb : d122306 q = 1) : d124318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, d124318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, d124318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8639 q = 1) (hb : d122306 q = 1) : d124319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8639, d124319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8639, d124319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8640 q = 1) (hb : d122306 q = 1) : d124320 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8640, d124320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8640, d124320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8641 q = 1) (hb : d122306 q = 1) : d124321 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8641, d124321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8641, d124321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21942 (p : Pattern) (ha : d94308 p = 1) (hb : d122306 p = 1) : d124327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8603 q = 1) (hb : d122306 q = 1) : d124290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8603, d124290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21936 q ha hb
    | true =>
      simp only [d8603, d124290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21934 q ha hb
  have h2 (q : Pattern) (ha : d8604 q = 1) (hb : d122306 q = 1) : d124291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8604, d124291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8604, d124291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8605 q = 1) (hb : d122306 q = 1) : d124292 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8605, d124292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8605, d124292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8606 q = 1) (hb : d122306 q = 1) : d124293 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8606, d124293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8606, d124293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8610 q = 1) (hb : d122306 q = 1) : d124300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8610, d124300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21937 q ha hb
    | true =>
      simp only [d8610, d124300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21935 q ha hb
  have h6 (q : Pattern) (ha : d8611 q = 1) (hb : d122306 q = 1) : d124301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8611, d124301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8611, d124301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8612 q = 1) (hb : d122306 q = 1) : d124302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8612, d124302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8612, d124302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8626 q = 1) (hb : d122306 q = 1) : d124316 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8626, d124316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21940 q ha hb
    | true =>
      simp only [d8626, d124316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21932 q ha hb
  have h9 (q : Pattern) (ha : d94304 q = 1) (hb : d122306 q = 1) : d124317 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94304, d124317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94304, d124317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8642 q = 1) (hb : d122306 q = 1) : d124322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8642, d124322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21941 q ha hb
    | true =>
      simp only [d8642, d124322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8643 q = 1) (hb : d122306 q = 1) : d124323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8643, d124323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8643, d124323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94305 q = 1) (hb : d122306 q = 1) : d124324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94305, d124324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94305, d124324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94306 q = 1) (hb : d122306 q = 1) : d124325 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94306, d124325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94306, d124325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94307 q = 1) (hb : d122306 q = 1) : d124326 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94307, d124326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94307, d124326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94308 q = 1) (hb : d122306 q = 1) : d124327 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94308, d124327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94308, d124327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro21943 (p : Pattern) (ha : d916 p = 1) (hb : d122306 p = 1) : d124329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21915 q ha hb
    | true =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d122306 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d122306 q = 1) : d124264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d122306 q = 1) : d124288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d916 q = 1) (hb : d122306 q = 1) : d124329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, d124329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d916, d124329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21944 (p : Pattern) (ha : d922 p = 1) (hb : d122306 p = 1) : d124335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21915 q ha hb
    | true =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d122306 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d122306 q = 1) : d124297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d122306 q = 1) : d124298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d922 q = 1) (hb : d122306 q = 1) : d124335 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, d124335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d922, d124335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21945 (p : Pattern) (ha : d8648 p = 1) (hb : d122306 p = 1) : d124328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21925 q ha hb
    | true =>
      simp only [d8577, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21915 q ha hb
    | true =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8579 q = 1) (hb : d122306 q = 1) : d124259 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8580 q = 1) (hb : d122306 q = 1) : d124260 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8580, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8580, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8601 q = 1) (hb : d122306 q = 1) : d124286 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8601, d124286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8601, d124286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8648 q = 1) (hb : d122306 q = 1) : d124328 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8648, d124328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8648, d124328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro21946 (p : Pattern) (ha : d8653 p = 1) (hb : d122306 p = 1) : d124334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21925 q ha hb
    | true =>
      simp only [d8577, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21915 q ha hb
    | true =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8579 q = 1) (hb : d122306 q = 1) : d124259 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8579, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8579, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8607 q = 1) (hb : d122306 q = 1) : d124294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8607, d124294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8607, d124294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8608 q = 1) (hb : d122306 q = 1) : d124295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8608, d124295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8608, d124295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8653 q = 1) (hb : d122306 q = 1) : d124334 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8653, d124334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8653, d124334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro21947 (p : Pattern) (ha : d8657 p = 1) (hb : d122306 p = 1) : d124339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8616 q = 1) (hb : d122306 q = 1) : d124310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8616, d124310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21939 q ha hb
    | true =>
      simp only [d8616, d124310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8617 q = 1) (hb : d122306 q = 1) : d124311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8617, d124311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8617, d124311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6878 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21931 q ha hb
    | true =>
      simp only [d6878, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6879 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8618 q = 1) (hb : d122306 q = 1) : d124312 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8618, d124312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8618, d124312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8619 q = 1) (hb : d122306 q = 1) : d124313 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8619, d124313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8619, d124313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8620 q = 1) (hb : d122306 q = 1) : d124314 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8620, d124314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8620, d124314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8657 q = 1) (hb : d122306 q = 1) : d124339 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8657, d124339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8657, d124339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro21948 (p : Pattern) (ha : d8658 p = 1) (hb : d122306 p = 1) : d124275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6878 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21931 q ha hb
    | true =>
      simp only [d6878, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6879 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6879, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21915 q ha hb
    | true =>
      simp only [d774, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8622 q = 1) (hb : d122306 q = 1) : d124259 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8622, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8622, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8623 q = 1) (hb : d122306 q = 1) : d124260 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8623, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8623, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8624 q = 1) (hb : d122306 q = 1) : d124261 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8624, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8624, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8658 q = 1) (hb : d122306 q = 1) : d124275 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8658, d124275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8658, d124275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro21949 (p : Pattern) (ha : d8663 p = 1) (hb : d122306 p = 1) : d124342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8577 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8577, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21925 q ha hb
    | true =>
      simp only [d8577, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8578 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8578, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8578, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8638 q = 1) (hb : d122306 q = 1) : d124318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8638, d124318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8638, d124318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8639 q = 1) (hb : d122306 q = 1) : d124319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8639, d124319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8639, d124319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8640 q = 1) (hb : d122306 q = 1) : d124320 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8640, d124320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8640, d124320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8663 q = 1) (hb : d122306 q = 1) : d124342 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8663, d124342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8663, d124342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21950 (p : Pattern) (ha : d94313 p = 1) (hb : d122306 p = 1) : d124348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8603 q = 1) (hb : d122306 q = 1) : d124290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8603, d124290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21936 q ha hb
    | true =>
      simp only [d8603, d124290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21934 q ha hb
  have h2 (q : Pattern) (ha : d8604 q = 1) (hb : d122306 q = 1) : d124291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8604, d124291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8604, d124291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8605 q = 1) (hb : d122306 q = 1) : d124292 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8605, d124292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8605, d124292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8606 q = 1) (hb : d122306 q = 1) : d124293 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8606, d124293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8606, d124293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8610 q = 1) (hb : d122306 q = 1) : d124300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8610, d124300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21937 q ha hb
    | true =>
      simp only [d8610, d124300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21935 q ha hb
  have h6 (q : Pattern) (ha : d8611 q = 1) (hb : d122306 q = 1) : d124301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8611, d124301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8611, d124301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8612 q = 1) (hb : d122306 q = 1) : d124302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8612, d124302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8612, d124302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8626 q = 1) (hb : d122306 q = 1) : d124316 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8626, d124316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21940 q ha hb
    | true =>
      simp only [d8626, d124316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21932 q ha hb
  have h9 (q : Pattern) (ha : d94304 q = 1) (hb : d122306 q = 1) : d124317 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94304, d124317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94304, d124317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8642 q = 1) (hb : d122306 q = 1) : d124322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8642, d124322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21941 q ha hb
    | true =>
      simp only [d8642, d124322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8643 q = 1) (hb : d122306 q = 1) : d124323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8643, d124323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8643, d124323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94305 q = 1) (hb : d122306 q = 1) : d124324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94305, d124324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94305, d124324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94306 q = 1) (hb : d122306 q = 1) : d124325 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94306, d124325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94306, d124325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94307 q = 1) (hb : d122306 q = 1) : d124326 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94307, d124326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94307, d124326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8649 q = 1) (hb : d122306 q = 1) : d124330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8649, d124330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21945 q ha hb
    | true =>
      simp only [d8649, d124330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21943 q ha hb
  have h16 (q : Pattern) (ha : d8650 q = 1) (hb : d122306 q = 1) : d124331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8650, d124331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8650, d124331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8651 q = 1) (hb : d122306 q = 1) : d124332 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8651, d124332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d8651, d124332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d8652 q = 1) (hb : d122306 q = 1) : d124333 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8652, d124333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8652, d124333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8654 q = 1) (hb : d122306 q = 1) : d124336 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8654, d124336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21946 q ha hb
    | true =>
      simp only [d8654, d124336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21944 q ha hb
  have h20 (q : Pattern) (ha : d8655 q = 1) (hb : d122306 q = 1) : d124337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8655, d124337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8655, d124337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d8656 q = 1) (hb : d122306 q = 1) : d124338 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8656, d124338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d8656, d124338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8659 q = 1) (hb : d122306 q = 1) : d124340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8659, d124340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21947 q ha hb
    | true =>
      simp only [d8659, d124340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21948 q ha hb
  have h23 (q : Pattern) (ha : d94309 q = 1) (hb : d122306 q = 1) : d124341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94309, d124341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94309, d124341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d8664 q = 1) (hb : d122306 q = 1) : d124343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8664, d124343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21949 q ha hb
    | true =>
      simp only [d8664, d124343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8665 q = 1) (hb : d122306 q = 1) : d124344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8665, d124344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8665, d124344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94310 q = 1) (hb : d122306 q = 1) : d124345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94310, d124345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94310, d124345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94311 q = 1) (hb : d122306 q = 1) : d124346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94311, d124346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94311, d124346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94312 q = 1) (hb : d122306 q = 1) : d124347 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94312, d124347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94312, d124347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94313 q = 1) (hb : d122306 q = 1) : d124348 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94313, d124348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94313, d124348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro21951 (p : Pattern) (ha : d94320 p = 1) (hb : d122306 p = 1) : d124368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8659 q = 1) (hb : d122306 q = 1) : d124340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8659, d124340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21947 q ha hb
    | true =>
      simp only [d8659, d124340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21948 q ha hb
  have h2 (q : Pattern) (ha : d94309 q = 1) (hb : d122306 q = 1) : d124341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94309, d124341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94309, d124341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8664 q = 1) (hb : d122306 q = 1) : d124343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8664, d124343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21949 q ha hb
    | true =>
      simp only [d8664, d124343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8665 q = 1) (hb : d122306 q = 1) : d124344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8665, d124344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8665, d124344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94310 q = 1) (hb : d122306 q = 1) : d124345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94310, d124345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94310, d124345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94318 q = 1) (hb : d122306 q = 1) : d124366 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94318, d124366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94318, d124366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94319 q = 1) (hb : d122306 q = 1) : d124367 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94319, d124367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94319, d124367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94320 q = 1) (hb : d122306 q = 1) : d124368 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94320, d124368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94320, d124368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21952 (p : Pattern) (ha : d976 p = 1) (hb : d122305 p = 1) : d124190 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d662 q = 1) : d662 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d415 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d663 q = 1) (hb : d122304 q = 1) : d14370 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d663, d122304, d14370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d663, d122304, d14370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d975 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d976 q = 1) (hb : d122305 q = 1) : d124190 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d976, d122305, d124190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d976, d122305, d124190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro21953 (p : Pattern) (ha : d6210 p = 1) (hb : d122305 p = 1) : d124032 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d415 q = 1) : d415 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d975 q = 1) (hb : d122304 q = 1) : d14154 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d122304, d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d975, d122304, d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6210 q = 1) (hb : d122305 q = 1) : d124032 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6210, d122305, d124032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6210, d122305, d124032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro21954 (p : Pattern) (ha : d6923 p = 1) (hb : d122306 p = 1) : d124390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d982 q = 1) (hb : d122305 q = 1) : d124191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21952 q ha hb
    | true =>
      simp only [d982, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21920 q ha hb
  have h2 (q : Pattern) (ha : d983 q = 1) (hb : d122305 q = 1) : d124192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d984 q = 1) (hb : d122305 q = 1) : d124193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6921 q = 1) (hb : d122306 q = 1) : d124194 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6921, d122306, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6921, d122306, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d986 q = 1) (hb : d122305 q = 1) : d986 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6211 q = 1) (hb : d122305 q = 1) : d124385 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21953 q ha hb
    | true =>
      simp only [d6211, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6212 q = 1) (hb : d122305 q = 1) : d124386 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6213 q = 1) (hb : d122305 q = 1) : d124387 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6214 q = 1) (hb : d122306 q = 1) : d124388 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d122306, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6214, d122306, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d6922 q = 1) (hb : d122306 q = 1) : d124389 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6922, d124389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6922, d124389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d6923 q = 1) (hb : d122306 q = 1) : d124390 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6923, d124390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6923, d124390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro21955 (p : Pattern) (ha : d970 p = 1) (hb : d122305 p = 1) : d124376 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d968 q = 1) : d968 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d662 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d969 q = 1) (hb : d122304 q = 1) : d14643 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d969, d122304, d14643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d969, d122304, d14643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d663 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d970 q = 1) (hb : d122305 q = 1) : d124376 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d970, d122305, d124376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d970, d122305, d124376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro21956 (p : Pattern) (ha : d8691 p = 1) (hb : d122306 p = 1) : d124382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d977 q = 1) (hb : d122305 q = 1) : d124377 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d977, d124377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21955 q ha hb
    | true =>
      simp only [d977, d124377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21952 q ha hb
  have h2 (q : Pattern) (ha : d978 q = 1) (hb : d122305 q = 1) : d124378 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d978, d124378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d978, d124378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d979 q = 1) (hb : d122305 q = 1) : d124379 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d979, d124379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d979, d124379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8689 q = 1) (hb : d122306 q = 1) : d124380 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8689, d122306, d124380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8689, d122306, d124380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d982 q = 1) (hb : d122305 q = 1) : d124191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21952 q ha hb
    | true =>
      simp only [d982, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21920 q ha hb
  have h7 (q : Pattern) (ha : d983 q = 1) (hb : d122305 q = 1) : d124192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d984 q = 1) (hb : d122305 q = 1) : d124193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6921 q = 1) (hb : d122306 q = 1) : d124194 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6921, d122306, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6921, d122306, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8690 q = 1) (hb : d122306 q = 1) : d124381 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8690, d124381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8690, d124381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8691 q = 1) (hb : d122306 q = 1) : d124382 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8691, d124382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8691, d124382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro21957 (p : Pattern) (ha : d8697 p = 1) (hb : d122306 p = 1) : d124396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8692 q = 1) (hb : d122306 q = 1) : d124383 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8692, d124383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21956 q ha hb
    | true =>
      simp only [d8692, d124383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8693 q = 1) (hb : d122306 q = 1) : d124384 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8693, d124384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8693, d124384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6924 q = 1) (hb : d122306 q = 1) : d124391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6924, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21954 q ha hb
    | true =>
      simp only [d6924, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6925 q = 1) (hb : d122306 q = 1) : d124392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6925, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6925, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8694 q = 1) (hb : d122306 q = 1) : d124393 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8694, d124393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8694, d124393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8695 q = 1) (hb : d122306 q = 1) : d124394 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8695, d124394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8695, d124394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8696 q = 1) (hb : d122306 q = 1) : d124395 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8696, d124395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8696, d124395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8697 q = 1) (hb : d122306 q = 1) : d124396 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8697, d124396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8697, d124396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro21958 (p : Pattern) (ha : d8701 p = 1) (hb : d122306 p = 1) : d124404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6924 q = 1) (hb : d122306 q = 1) : d124391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6924, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21954 q ha hb
    | true =>
      simp only [d6924, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6925 q = 1) (hb : d122306 q = 1) : d124392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6925, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6925, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d122306 q = 1) : d124399 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21921 q ha hb
    | true =>
      simp only [d1006, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d122306 q = 1) : d124400 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8698 q = 1) (hb : d122306 q = 1) : d124401 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8698, d124401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8698, d124401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8699 q = 1) (hb : d122306 q = 1) : d124402 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8699, d124402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8699, d124402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8700 q = 1) (hb : d122306 q = 1) : d124403 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8700, d124403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8700, d124403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8701 q = 1) (hb : d122306 q = 1) : d124404 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8701, d124404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8701, d124404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro21959 (p : Pattern) (ha : d8715 p = 1) (hb : d122306 p = 1) : d124390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d982 q = 1) (hb : d122305 q = 1) : d124191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21952 q ha hb
    | true =>
      simp only [d982, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21920 q ha hb
  have h2 (q : Pattern) (ha : d983 q = 1) (hb : d122305 q = 1) : d124192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d984 q = 1) (hb : d122305 q = 1) : d124193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6921 q = 1) (hb : d122306 q = 1) : d124194 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6921, d122306, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6921, d122306, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d986 q = 1) (hb : d122305 q = 1) : d986 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d987 q = 1) (hb : d122305 q = 1) : d124385 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21920 q ha hb
    | true =>
      simp only [d987, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d988 q = 1) (hb : d122305 q = 1) : d124386 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d989 q = 1) (hb : d122305 q = 1) : d124387 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d995 q = 1) (hb : d122306 q = 1) : d124388 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d122306, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d995, d122306, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d8714 q = 1) (hb : d122306 q = 1) : d124389 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8714, d124389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8714, d124389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8715 q = 1) (hb : d122306 q = 1) : d124390 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8715, d124390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8715, d124390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro21960 (p : Pattern) (ha : d8721 p = 1) (hb : d122306 p = 1) : d124410 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8716 q = 1) (hb : d122306 q = 1) : d124391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8716, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21959 q ha hb
    | true =>
      simp only [d8716, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8717 q = 1) (hb : d122306 q = 1) : d124392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8717, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8717, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8718 q = 1) (hb : d122306 q = 1) : d124407 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8718, d124407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8718, d124407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8719 q = 1) (hb : d122306 q = 1) : d124408 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8719, d124408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8719, d124408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8720 q = 1) (hb : d122306 q = 1) : d124409 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8720, d124409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8720, d124409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8721 q = 1) (hb : d122306 q = 1) : d124410 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8721, d124410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8721, d124410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21961 (p : Pattern) (ha : d94330 p = 1) (hb : d122306 p = 1) : d124416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8702 q = 1) (hb : d122306 q = 1) : d124405 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8702, d124405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21957 q ha hb
    | true =>
      simp only [d8702, d124405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21958 q ha hb
  have h2 (q : Pattern) (ha : d94326 q = 1) (hb : d122306 q = 1) : d124406 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94326, d124406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94326, d124406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8722 q = 1) (hb : d122306 q = 1) : d124411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8722, d124411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21960 q ha hb
    | true =>
      simp only [d8722, d124411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8723 q = 1) (hb : d122306 q = 1) : d124412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8723, d124412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8723, d124412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94327 q = 1) (hb : d122306 q = 1) : d124413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94327, d124413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94327, d124413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94328 q = 1) (hb : d122306 q = 1) : d124414 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94328, d124414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94328, d124414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94329 q = 1) (hb : d122306 q = 1) : d124415 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94329, d124415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94329, d124415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94330 q = 1) (hb : d122306 q = 1) : d124416 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94330, d124416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94330, d124416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21962 (p : Pattern) (ha : d94336 p = 1) (hb : d122306 p = 1) : d124433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8589 q = 1) (hb : d122306 q = 1) : d124273 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8589, d124273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8589, d124273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21927 q ha hb
  have h2 (q : Pattern) (ha : d8590 q = 1) (hb : d122306 q = 1) : d124274 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8590, d124274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8590, d124274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8598 q = 1) (hb : d122306 q = 1) : d124283 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8598, d124283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21927 q ha hb
    | true =>
      simp only [d8598, d124283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21929 q ha hb
  have h4 (q : Pattern) (ha : d8599 q = 1) (hb : d122306 q = 1) : d124284 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8599, d124284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8599, d124284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8600 q = 1) (hb : d122306 q = 1) : d124285 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8600, d124285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8600, d124285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94314 q = 1) (hb : d122306 q = 1) : d124349 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94314, d124349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21942 q ha hb
    | true =>
      simp only [d94314, d124349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21950 q ha hb
  have h7 (q : Pattern) (ha : d8677 q = 1) (hb : d122306 q = 1) : d124362 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8677, d124362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21933 q ha hb
    | true =>
      simp only [d8677, d124362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21918 q ha hb
  have h8 (q : Pattern) (ha : d94315 q = 1) (hb : d122306 q = 1) : d124363 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94315, d124363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94315, d124363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94316 q = 1) (hb : d122306 q = 1) : d124364 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94316, d124364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94316, d124364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94317 q = 1) (hb : d122306 q = 1) : d124365 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94317, d124365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94317, d124365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94321 q = 1) (hb : d122306 q = 1) : d124369 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94321, d124369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94321, d124369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21951 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d122306 q = 1) : d124371 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d124371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d124371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21919 q ha hb
  have h13 (q : Pattern) (ha : d94322 q = 1) (hb : d122306 q = 1) : d124372 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94322, d124372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94322, d124372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94323 q = 1) (hb : d122306 q = 1) : d124373 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94323, d124373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94323, d124373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94324 q = 1) (hb : d122306 q = 1) : d124374 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94324, d124374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94324, d124374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94325 q = 1) (hb : d122306 q = 1) : d124375 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94325, d124375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94325, d124375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94331 q = 1) (hb : d122306 q = 1) : d124417 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94331, d124417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94331, d124417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21961 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d122306 q = 1) : d124428 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d124428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d124428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21923 q ha hb
  have h19 (q : Pattern) (ha : d94332 q = 1) (hb : d122306 q = 1) : d124429 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94332, d124429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94332, d124429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d94333 q = 1) (hb : d122306 q = 1) : d124430 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94333, d124430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94333, d124430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94334 q = 1) (hb : d122306 q = 1) : d124431 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94334, d124431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94334, d124431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94335 q = 1) (hb : d122306 q = 1) : d124432 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94335, d124432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94335, d124432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94336 q = 1) (hb : d122306 q = 1) : d124433 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94336, d124433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94336, d124433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro21963 (p : Pattern) (ha : d94342 p = 1) (hb : d122306 p = 1) : d124439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94337 q = 1) (hb : d122306 q = 1) : d124434 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94337, d124434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94337, d124434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21962 q ha hb
  have h2 (q : Pattern) (ha : d94338 q = 1) (hb : d122306 q = 1) : d124435 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94338, d124435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94338, d124435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94339 q = 1) (hb : d122306 q = 1) : d124436 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94339, d124436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94339, d124436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94340 q = 1) (hb : d122306 q = 1) : d124437 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94340, d124437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94340, d124437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94341 q = 1) (hb : d122306 q = 1) : d124438 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94341, d124438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94341, d124438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94342 q = 1) (hb : d122306 q = 1) : d124439 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94342, d124439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94342, d124439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21964 (p : Pattern) (ha : d1128 p = 1) (hb : d122305 p = 1) : d124443 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1113 q = 1) : d1113 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1124 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1125 q = 1) (hb : d122304 q = 1) : d14762 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d122304, d14762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1125, d122304, d14762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1127 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1128 q = 1) (hb : d122305 q = 1) : d124443 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1128, d122305, d124443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1128, d122305, d124443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro21965 (p : Pattern) (ha : d1141 p = 1) (hb : d122305 p = 1) : d12961 p = 1 := by
  have h0 (q : Pattern) (ha : d1127 q = 1) (hb : d122304 q = 1) : d1127 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1140 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1141 q = 1) (hb : d122305 q = 1) : d12961 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1141, d122305, d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1141, d122305, d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro21966 (p : Pattern) (ha : d1152 p = 1) (hb : d122306 p = 1) : d124457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1142 q = 1) (hb : d122305 q = 1) : d124448 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21964 q ha hb
    | true =>
      simp only [d1142, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21965 q ha hb
  have h2 (q : Pattern) (ha : d1143 q = 1) (hb : d122305 q = 1) : d124449 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1144 q = 1) (hb : d122305 q = 1) : d124450 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1146 q = 1) (hb : d122306 q = 1) : d124451 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1146, d122306, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1146, d122306, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1151 q = 1) (hb : d122306 q = 1) : d124456 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1151, d124456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1151, d124456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1152 q = 1) (hb : d122306 q = 1) : d124457 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1152, d124457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1152, d124457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro21967 (p : Pattern) (ha : d1162 p = 1) (hb : d122306 p = 1) : d124467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d122306 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21966 q ha hb
    | true =>
      simp only [d1153, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d122306 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d122306 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d122306 q = 1) : d124465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1161 q = 1) (hb : d122306 q = 1) : d124466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1161, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1162 q = 1) (hb : d122306 q = 1) : d124467 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1162, d124467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1162, d124467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21968 (p : Pattern) (ha : d1172 p = 1) (hb : d122306 p = 1) : d124477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d122306 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21966 q ha hb
    | true =>
      simp only [d1153, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d122306 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d122306 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d122306 q = 1) : d124465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1161 q = 1) (hb : d122306 q = 1) : d124466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1161, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1172 q = 1) (hb : d122306 q = 1) : d124477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1172, d124477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1172, d124477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21969 (p : Pattern) (ha : d1361 p = 1) (hb : d122306 p = 1) : d124580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1350 q = 1) (hb : d122306 q = 1) : d124569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21967 q ha hb
    | true =>
      simp only [d1350, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1351 q = 1) (hb : d122306 q = 1) : d124570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1352 q = 1) (hb : d122306 q = 1) : d124571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1352, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1353 q = 1) (hb : d122306 q = 1) : d124572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1354 q = 1) (hb : d122306 q = 1) : d124573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1356 q = 1) (hb : d122306 q = 1) : d124575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21968 q ha hb
    | true =>
      simp only [d1356, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1357 q = 1) (hb : d122306 q = 1) : d124576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1358 q = 1) (hb : d122306 q = 1) : d124577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1358, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1359 q = 1) (hb : d122306 q = 1) : d124578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1360 q = 1) (hb : d122306 q = 1) : d124579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1361 q = 1) (hb : d122306 q = 1) : d124580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1361, d124580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1361, d124580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21970 (p : Pattern) (ha : d1370 p = 1) (hb : d122306 p = 1) : d124589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1356 q = 1) (hb : d122306 q = 1) : d124575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21968 q ha hb
    | true =>
      simp only [d1356, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1357 q = 1) (hb : d122306 q = 1) : d124576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1358 q = 1) (hb : d122306 q = 1) : d124577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1358, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1359 q = 1) (hb : d122306 q = 1) : d124578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1360 q = 1) (hb : d122306 q = 1) : d124579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1370 q = 1) (hb : d122306 q = 1) : d124589 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1370, d124589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1370, d124589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21971 (p : Pattern) (ha : d1401 p = 1) (hb : d122305 p = 1) : d124601 p = 1 := by
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
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1400 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1401 q = 1) (hb : d122305 q = 1) : d124601 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1401, d122305, d124601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1401, d122305, d124601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro21972 (p : Pattern) (ha : d1411 p = 1) (hb : d122305 p = 1) : d13190 p = 1 := by
  have h0 (q : Pattern) (ha : d1400 q = 1) (hb : d122304 q = 1) : d1400 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1410 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1411 q = 1) (hb : d122305 q = 1) : d13190 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1411, d122305, d13190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1411, d122305, d13190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro21973 (p : Pattern) (ha : d1430 p = 1) (hb : d122306 p = 1) : d124627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1412 q = 1) (hb : d122305 q = 1) : d124622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21971 q ha hb
    | true =>
      simp only [d1412, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21972 q ha hb
  have h2 (q : Pattern) (ha : d1413 q = 1) (hb : d122305 q = 1) : d124623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1414 q = 1) (hb : d122305 q = 1) : d124624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1420 q = 1) (hb : d122306 q = 1) : d124625 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d122306, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1420, d122306, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1429 q = 1) (hb : d122306 q = 1) : d124626 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1429, d124626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1429, d124626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1430 q = 1) (hb : d122306 q = 1) : d124627 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1430, d124627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1430, d124627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro21974 (p : Pattern) (ha : d1497 p = 1) (hb : d122306 p = 1) : d124654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1431 q = 1) (hb : d122306 q = 1) : d124628 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21973 q ha hb
    | true =>
      simp only [d1431, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1432 q = 1) (hb : d122306 q = 1) : d124629 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1494 q = 1) (hb : d122306 q = 1) : d124651 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1494, d124651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1494, d124651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1495 q = 1) (hb : d122306 q = 1) : d124652 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1495, d124652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1495, d124652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1496 q = 1) (hb : d122306 q = 1) : d124653 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1496, d124653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1496, d124653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1497 q = 1) (hb : d122306 q = 1) : d124654 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1497, d124654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1497, d124654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21975 (p : Pattern) (ha : d1503 p = 1) (hb : d122306 p = 1) : d124660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1498 q = 1) (hb : d122306 q = 1) : d124655 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1498, d124655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21974 q ha hb
    | true =>
      simp only [d1498, d124655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1499 q = 1) (hb : d122306 q = 1) : d124656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1499, d124656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1499, d124656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1500 q = 1) (hb : d122306 q = 1) : d124657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1500, d124657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1500, d124657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1501 q = 1) (hb : d122306 q = 1) : d124658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1501, d124658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1501, d124658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1502 q = 1) (hb : d122306 q = 1) : d124659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1502, d124659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1502, d124659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1503 q = 1) (hb : d122306 q = 1) : d124660 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1503, d124660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1503, d124660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21976 (p : Pattern) (ha : d1126 p = 1) (hb : d122305 p = 1) : d124442 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1103 q = 1) : d1103 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1113 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1114 q = 1) (hb : d122304 q = 1) : d14757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1114, d122304, d14757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1114, d122304, d14757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1125 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1126 q = 1) (hb : d122305 q = 1) : d124442 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1126, d122305, d124442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1126, d122305, d124442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro21977 (p : Pattern) (ha : d8743 p = 1) (hb : d122306 p = 1) : d124453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1129 q = 1) (hb : d122305 q = 1) : d124444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21976 q ha hb
    | true =>
      simp only [d1129, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21964 q ha hb
  have h2 (q : Pattern) (ha : d1130 q = 1) (hb : d122305 q = 1) : d124445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1131 q = 1) (hb : d122305 q = 1) : d124446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6954 q = 1) (hb : d122306 q = 1) : d124447 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6954, d122306, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6954, d122306, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1142 q = 1) (hb : d122305 q = 1) : d124448 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21964 q ha hb
    | true =>
      simp only [d1142, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21965 q ha hb
  have h7 (q : Pattern) (ha : d1143 q = 1) (hb : d122305 q = 1) : d124449 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1144 q = 1) (hb : d122305 q = 1) : d124450 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1146 q = 1) (hb : d122306 q = 1) : d124451 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1146, d122306, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1146, d122306, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8742 q = 1) (hb : d122306 q = 1) : d124452 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8742, d124452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8742, d124452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8743 q = 1) (hb : d122306 q = 1) : d124453 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8743, d124453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8743, d124453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro21978 (p : Pattern) (ha : d8749 p = 1) (hb : d122306 p = 1) : d124463 p = 1 := by
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
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d122306 q = 1) : d124460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8747 q = 1) (hb : d122306 q = 1) : d124461 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8747, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8748 q = 1) (hb : d122306 q = 1) : d124462 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8748, d124462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8748, d124462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8749 q = 1) (hb : d122306 q = 1) : d124463 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8749, d124463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8749, d124463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21979 (p : Pattern) (ha : d8755 p = 1) (hb : d122306 p = 1) : d124473 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8750 q = 1) (hb : d122306 q = 1) : d124468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8750, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21978 q ha hb
    | true =>
      simp only [d8750, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21967 q ha hb
  have h2 (q : Pattern) (ha : d8751 q = 1) (hb : d122306 q = 1) : d124469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8751, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8751, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8752 q = 1) (hb : d122306 q = 1) : d124470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8752, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8752, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8753 q = 1) (hb : d122306 q = 1) : d124471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8753, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8753, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8754 q = 1) (hb : d122306 q = 1) : d124472 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8754, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8754, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8755 q = 1) (hb : d122306 q = 1) : d124473 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8755, d124473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8755, d124473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21980 (p : Pattern) (ha : d8758 p = 1) (hb : d122306 p = 1) : d124476 p = 1 := by
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
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d122306 q = 1) : d124460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8747 q = 1) (hb : d122306 q = 1) : d124461 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8747, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8748 q = 1) (hb : d122306 q = 1) : d124462 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8748, d124462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8748, d124462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8758 q = 1) (hb : d122306 q = 1) : d124476 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8758, d124476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8758, d124476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro21981 (p : Pattern) (ha : d8764 p = 1) (hb : d122306 p = 1) : d124483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8750 q = 1) (hb : d122306 q = 1) : d124468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8750, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21978 q ha hb
    | true =>
      simp only [d8750, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21967 q ha hb
  have h2 (q : Pattern) (ha : d8751 q = 1) (hb : d122306 q = 1) : d124469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8751, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8751, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8752 q = 1) (hb : d122306 q = 1) : d124470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8752, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8752, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8753 q = 1) (hb : d122306 q = 1) : d124471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8753, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8753, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8754 q = 1) (hb : d122306 q = 1) : d124472 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8754, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8754, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8759 q = 1) (hb : d122306 q = 1) : d124478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8759, d124478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21980 q ha hb
    | true =>
      simp only [d8759, d124478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21968 q ha hb
  have h7 (q : Pattern) (ha : d8760 q = 1) (hb : d122306 q = 1) : d124479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8760, d124479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8760, d124479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8761 q = 1) (hb : d122306 q = 1) : d124480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8761, d124480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8761, d124480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8762 q = 1) (hb : d122306 q = 1) : d124481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8762, d124481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8762, d124481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8763 q = 1) (hb : d122306 q = 1) : d124482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8763, d124482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8763, d124482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8764 q = 1) (hb : d122306 q = 1) : d124483 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8764, d124483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8764, d124483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21982 (p : Pattern) (ha : d5009 p = 1) (hb : d122305 p = 1) : d124443 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1113 q = 1) : d1113 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1124 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1125 q = 1) (hb : d122304 q = 1) : d14762 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d122304, d14762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1125, d122304, d14762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5009 q = 1) (hb : d122305 q = 1) : d124443 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5009, d122305, d124443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5009, d122305, d124443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro21983 (p : Pattern) (ha : d6956 p = 1) (hb : d122306 p = 1) : d124518 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1129 q = 1) (hb : d122305 q = 1) : d124444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21976 q ha hb
    | true =>
      simp only [d1129, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21964 q ha hb
  have h2 (q : Pattern) (ha : d1130 q = 1) (hb : d122305 q = 1) : d124445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1131 q = 1) (hb : d122305 q = 1) : d124446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6954 q = 1) (hb : d122306 q = 1) : d124447 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6954, d122306, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6954, d122306, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5023 q = 1) (hb : d122305 q = 1) : d5023 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5024 q = 1) (hb : d122305 q = 1) : d124513 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21982 q ha hb
    | true =>
      simp only [d5024, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5025 q = 1) (hb : d122305 q = 1) : d124514 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5026 q = 1) (hb : d122305 q = 1) : d124515 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5027 q = 1) (hb : d122306 q = 1) : d124516 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5027, d122306, d124516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5027, d122306, d124516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d6955 q = 1) (hb : d122306 q = 1) : d124517 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6955, d124517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6955, d124517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d6956 q = 1) (hb : d122306 q = 1) : d124518 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6956, d124518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6956, d124518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro21984 (p : Pattern) (ha : d8792 p = 1) (hb : d122306 p = 1) : d124528 p = 1 := by
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
  have h8 (q : Pattern) (ha : d8792 q = 1) (hb : d122306 q = 1) : d124528 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8792, d124528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8792, d124528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21985 (p : Pattern) (ha : d8843 p = 1) (hb : d122306 p = 1) : d124574 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8838 q = 1) (hb : d122306 q = 1) : d124564 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8838, d124564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21984 q ha hb
    | true =>
      simp only [d8838, d124564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21967 q ha hb
  have h2 (q : Pattern) (ha : d8839 q = 1) (hb : d122306 q = 1) : d124565 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8839, d124565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8839, d124565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8840 q = 1) (hb : d122306 q = 1) : d124566 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8840, d124566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8840, d124566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8841 q = 1) (hb : d122306 q = 1) : d124567 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8841, d124567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8841, d124567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8842 q = 1) (hb : d122306 q = 1) : d124568 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8842, d124568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8842, d124568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1350 q = 1) (hb : d122306 q = 1) : d124569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21967 q ha hb
    | true =>
      simp only [d1350, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1351 q = 1) (hb : d122306 q = 1) : d124570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1352 q = 1) (hb : d122306 q = 1) : d124571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1352, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1353 q = 1) (hb : d122306 q = 1) : d124572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1354 q = 1) (hb : d122306 q = 1) : d124573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8843 q = 1) (hb : d122306 q = 1) : d124574 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8843, d124574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8843, d124574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro21986 (p : Pattern) (ha : d1185 p = 1) (hb : d122306 p = 1) : d124490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d122306 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21966 q ha hb
    | true =>
      simp only [d1153, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d122306 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d122306 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d122306 q = 1) : d124465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1184 q = 1) (hb : d122306 q = 1) : d124489 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1185 q = 1) (hb : d122306 q = 1) : d124490 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1185, d124490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1185, d124490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21987 (p : Pattern) (ha : d1195 p = 1) (hb : d122306 p = 1) : d124500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d122306 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21966 q ha hb
    | true =>
      simp only [d1153, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d122306 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d122306 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1193 q = 1) (hb : d122306 q = 1) : d124498 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1194 q = 1) (hb : d122306 q = 1) : d124499 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1194, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d122306 q = 1) : d124500 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1195, d124500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1195, d124500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21988 (p : Pattern) (ha : d8769 p = 1) (hb : d122306 p = 1) : d124488 p = 1 := by
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
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d122306 q = 1) : d124460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8747 q = 1) (hb : d122306 q = 1) : d124461 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8747, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8768 q = 1) (hb : d122306 q = 1) : d124487 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8768, d124487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8768, d124487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8769 q = 1) (hb : d122306 q = 1) : d124488 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8769, d124488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8769, d124488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21989 (p : Pattern) (ha : d8776 p = 1) (hb : d122306 p = 1) : d124497 p = 1 := by
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
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d122306 q = 1) : d124460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8774 q = 1) (hb : d122306 q = 1) : d124495 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8774, d124495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8774, d124495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8775 q = 1) (hb : d122306 q = 1) : d124496 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8775, d124496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8775, d124496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8776 q = 1) (hb : d122306 q = 1) : d124497 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8776, d124497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8776, d124497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21990 (p : Pattern) (ha : d1215 p = 1) (hb : d122305 p = 1) : d124504 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1213 q = 1) : d1213 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1103 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1214 q = 1) (hb : d122304 q = 1) : d14835 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1214, d122304, d14835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1214, d122304, d14835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1114 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1215 q = 1) (hb : d122305 q = 1) : d124504 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1215, d122305, d124504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1215, d122305, d124504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro21991 (p : Pattern) (ha : d8782 p = 1) (hb : d122306 p = 1) : d124510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1216 q = 1) (hb : d122305 q = 1) : d124505 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1216, d124505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21990 q ha hb
    | true =>
      simp only [d1216, d124505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21976 q ha hb
  have h2 (q : Pattern) (ha : d1217 q = 1) (hb : d122305 q = 1) : d124506 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1217, d124506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1217, d124506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1218 q = 1) (hb : d122305 q = 1) : d124507 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1218, d124507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1218, d124507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8780 q = 1) (hb : d122306 q = 1) : d124508 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8780, d122306, d124508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8780, d122306, d124508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1129 q = 1) (hb : d122305 q = 1) : d124444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21976 q ha hb
    | true =>
      simp only [d1129, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21964 q ha hb
  have h7 (q : Pattern) (ha : d1130 q = 1) (hb : d122305 q = 1) : d124445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1131 q = 1) (hb : d122305 q = 1) : d124446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6954 q = 1) (hb : d122306 q = 1) : d124447 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6954, d122306, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6954, d122306, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d8781 q = 1) (hb : d122306 q = 1) : d124509 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8781, d124509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8781, d124509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8782 q = 1) (hb : d122306 q = 1) : d124510 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8782, d124510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8782, d124510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro21992 (p : Pattern) (ha : d8788 p = 1) (hb : d122306 p = 1) : d124524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8783 q = 1) (hb : d122306 q = 1) : d124511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8783, d124511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21991 q ha hb
    | true =>
      simp only [d8783, d124511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8784 q = 1) (hb : d122306 q = 1) : d124512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8784, d124512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8784, d124512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6957 q = 1) (hb : d122306 q = 1) : d124519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21983 q ha hb
    | true =>
      simp only [d6957, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6958 q = 1) (hb : d122306 q = 1) : d124520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8785 q = 1) (hb : d122306 q = 1) : d124521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8785, d124521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8785, d124521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8786 q = 1) (hb : d122306 q = 1) : d124522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8786, d124522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8786, d124522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8787 q = 1) (hb : d122306 q = 1) : d124523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8787, d124523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8787, d124523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8788 q = 1) (hb : d122306 q = 1) : d124524 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8788, d124524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8788, d124524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro21993 (p : Pattern) (ha : d8808 p = 1) (hb : d122306 p = 1) : d124534 p = 1 := by
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
  have h6 (q : Pattern) (ha : d8808 q = 1) (hb : d122306 q = 1) : d124534 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8808, d124534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8808, d124534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro21994 (p : Pattern) (ha : d94349 p = 1) (hb : d122306 p = 1) : d124540 p = 1 := by
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
  have h15 (q : Pattern) (ha : d94349 q = 1) (hb : d122306 q = 1) : d124540 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94349, d124540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94349, d124540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro21995 (p : Pattern) (ha : d1327 p = 1) (hb : d122306 p = 1) : d124542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d122306 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21966 q ha hb
    | true =>
      simp only [d1153, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d122306 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d122306 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d122306 q = 1) : d124465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1184 q = 1) (hb : d122306 q = 1) : d124489 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1327 q = 1) (hb : d122306 q = 1) : d124542 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1327, d124542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1327, d124542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21996 (p : Pattern) (ha : d1333 p = 1) (hb : d122306 p = 1) : d124548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d122306 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21966 q ha hb
    | true =>
      simp only [d1153, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d122306 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d122306 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1193 q = 1) (hb : d122306 q = 1) : d124498 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1194 q = 1) (hb : d122306 q = 1) : d124499 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1194, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1333 q = 1) (hb : d122306 q = 1) : d124548 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1333, d124548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1333, d124548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro21997 (p : Pattern) (ha : d8815 p = 1) (hb : d122306 p = 1) : d124541 p = 1 := by
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
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d122306 q = 1) : d124460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8747 q = 1) (hb : d122306 q = 1) : d124461 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8747, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8747, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8768 q = 1) (hb : d122306 q = 1) : d124487 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8768, d124487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8768, d124487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8815 q = 1) (hb : d122306 q = 1) : d124541 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8815, d124541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8815, d124541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro21998 (p : Pattern) (ha : d8820 p = 1) (hb : d122306 p = 1) : d124547 p = 1 := by
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
  have h5 (q : Pattern) (ha : d8746 q = 1) (hb : d122306 q = 1) : d124460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8746, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8746, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8774 q = 1) (hb : d122306 q = 1) : d124495 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8774, d124495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8774, d124495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8775 q = 1) (hb : d122306 q = 1) : d124496 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8775, d124496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8775, d124496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8820 q = 1) (hb : d122306 q = 1) : d124547 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8820, d124547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8820, d124547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro21999 (p : Pattern) (ha : d8824 p = 1) (hb : d122306 p = 1) : d124552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8783 q = 1) (hb : d122306 q = 1) : d124511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8783, d124511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21991 q ha hb
    | true =>
      simp only [d8783, d124511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8784 q = 1) (hb : d122306 q = 1) : d124512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8784, d124512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8784, d124512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6957 q = 1) (hb : d122306 q = 1) : d124519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21983 q ha hb
    | true =>
      simp only [d6957, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6958 q = 1) (hb : d122306 q = 1) : d124520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6958, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8785 q = 1) (hb : d122306 q = 1) : d124521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8785, d124521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8785, d124521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8786 q = 1) (hb : d122306 q = 1) : d124522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8786, d124522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8786, d124522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8787 q = 1) (hb : d122306 q = 1) : d124523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8787, d124523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8787, d124523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8824 q = 1) (hb : d122306 q = 1) : d124552 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8824, d124552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8824, d124552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
