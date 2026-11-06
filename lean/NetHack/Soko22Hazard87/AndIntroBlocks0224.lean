import NetHack.Soko22Hazard87.AndIntroBlocks0223
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro56000 (p : Pattern) (ha : d53865 p = 1) (hb : d194336 p = 1) : d53865 p = 1 := by
  have h0 (q : Pattern) (ha : d53865 q = 1) (hb : d194336 q = 1) : d53865 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro56001 (p : Pattern) (ha : d74825 p = 1) (hb : d227687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74819 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d74820 q = 1) (hb : d227686 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d74820, d227686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74820, d227686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d74821 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d74821, d227687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74821, d227687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d74822 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d74822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74823 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d74823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d74824 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d74824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d74825 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d74825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro56002 (p : Pattern) (ha : d74831 p = 1) (hb : d227687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74826 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d74826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56001 q ha hb
    | true =>
      simp only [d74826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74827 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d74827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74828 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d74828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74829 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d74829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74830 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74831 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56003 (p : Pattern) (ha : d74837 p = 1) (hb : d227687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74832 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56002 q ha hb
    | true =>
      simp only [d74832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74833 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74834 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74835 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74836 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74837 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
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
theorem andIntro56004 (p : Pattern) (ha : d74843 p = 1) (hb : d227687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74838 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56003 q ha hb
    | true =>
      simp only [d74838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74839 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74840 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74841 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74842 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74843 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
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
theorem andIntro56005 (p : Pattern) (ha : d74849 p = 1) (hb : d227687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74844 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56004 q ha hb
    | true =>
      simp only [d74844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74845 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74846 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74847 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74848 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74849 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
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
theorem andIntro56006 (p : Pattern) (ha : d0 p = 1) (hb : d230874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d230874 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro56007 (p : Pattern) (ha : d53841 p = 1) (hb : d227687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53835 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53836 q = 1) (hb : d227686 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, d227686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53836, d227686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53837 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, d227687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53837, d227687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53838 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53839 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d53840 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d53841 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro56008 (p : Pattern) (ha : d53847 p = 1) (hb : d227687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56007 q ha hb
    | true =>
      simp only [d53842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53844 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53846 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53847 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56009 (p : Pattern) (ha : d53853 p = 1) (hb : d227687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56008 q ha hb
    | true =>
      simp only [d53848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
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
theorem andIntro56010 (p : Pattern) (ha : d53859 p = 1) (hb : d227687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56009 q ha hb
    | true =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
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
theorem andIntro56011 (p : Pattern) (ha : d53865 p = 1) (hb : d227687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56010 q ha hb
    | true =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d227687 q = 1) : d0 q = 1 := by
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
theorem andIntro56012 (p : Pattern) (ha : d0 p = 1) (hb : d231165 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231165 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro56013 (p : Pattern) (ha : d138 p = 1) (hb : d208033 p = 1) : d9381 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d135 q = 1) : d135 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d136 q = 1) (hb : d208033 q = 1) : d5448 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d208033, d5448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136, d208033, d5448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d137 q = 1) (hb : d208033 q = 1) : d5449 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d5449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137, d5449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23 q = 1) (hb : d208033 q = 1) : d23 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d138 q = 1) (hb : d208033 q = 1) : d9381 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d138, d9381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138, d9381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56014 (p : Pattern) (ha : d144 p = 1) (hb : d208033 p = 1) : d16081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d208033 q = 1) : d9382 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56013 q ha hb
    | true =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d140 q = 1) (hb : d208033 q = 1) : d9384 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d141 q = 1) (hb : d208033 q = 1) : d12493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d208033 q = 1) : d12494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d142, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d208033 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d143 q = 1) (hb : d208033 q = 1) : d12495 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d143, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d208033 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d144 q = 1) (hb : d208033 q = 1) : d16081 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, d16081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144, d16081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56015 (p : Pattern) (ha : d150 p = 1) (hb : d208033 p = 1) : d23140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d208033 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d208033 q = 1) : d23135 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56014 q ha hb
    | true =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d208033 q = 1) : d23136 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d208033 q = 1) : d23137 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d208033 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148 q = 1) (hb : d208033 q = 1) : d23138 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d23138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148, d23138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d208033 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d149 q = 1) (hb : d208033 q = 1) : d23139 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d23139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d149, d23139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150 q = 1) (hb : d208033 q = 1) : d23140 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, d23140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150, d23140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro56016 (p : Pattern) (ha : d203 p = 1) (hb : d208033 p = 1) : d23153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d208033 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56015 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d208033 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208033 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d208033 q = 1) : d23143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d208033 q = 1) : d23144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d23144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d23144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d208033 q = 1) : d23145 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d23145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d23145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d203 q = 1) (hb : d208033 q = 1) : d23153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, d23153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d203, d23153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro56017 (p : Pattern) (ha : d4349 p = 1) (hb : d208033 p = 1) : d211098 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d208033 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d208033 q = 1) : d23154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d23154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56016 q ha hb
    | true =>
      simp only [d204, d23154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4340 q = 1) (hb : d208033 q = 1) : d211087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d211087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4340, d211087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d208033 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4341 q = 1) (hb : d208033 q = 1) : d211088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d211088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4341, d211088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4342 q = 1) (hb : d208033 q = 1) : d211096 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d211096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d211096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4343 q = 1) (hb : d208033 q = 1) : d211097 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d211097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d211097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4349 q = 1) (hb : d208033 q = 1) : d211098 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d211098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d211098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56018 (p : Pattern) (ha : d231 p = 1) (hb : d208033 p = 1) : d16166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d208033 q = 1) : d12599 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d12599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d12599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56013 q ha hb
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d208033 q = 1) : d9382 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56013 q ha hb
    | true =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d227 q = 1) (hb : d208033 q = 1) : d12600 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d12600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d227, d12600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d208033 q = 1) : d9384 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d208033 q = 1) : d12601 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d12601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d12601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d208033 q = 1) : d12602 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d12602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d12602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d208033 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d230 q = 1) (hb : d208033 q = 1) : d12603 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d12603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d230, d12603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d208033 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d231 q = 1) (hb : d208033 q = 1) : d16166 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d16166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d231, d16166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro56019 (p : Pattern) (ha : d237 p = 1) (hb : d208033 p = 1) : d23177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d208033 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d208033 q = 1) : d23172 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d23172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56018 q ha hb
    | true =>
      simp only [d232, d23172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d208033 q = 1) : d23173 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d23173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d23173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d208033 q = 1) : d23174 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d23174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d23174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d208033 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d235 q = 1) (hb : d208033 q = 1) : d23175 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d23175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235, d23175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d208033 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d236 q = 1) (hb : d208033 q = 1) : d23176 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d23176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236, d23176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237 q = 1) (hb : d208033 q = 1) : d23177 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d23177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237, d23177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro56020 (p : Pattern) (ha : d243 p = 1) (hb : d208033 p = 1) : d23183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d208033 q = 1) : d23178 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d23178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56019 q ha hb
    | true =>
      simp only [d238, d23178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d208033 q = 1) : d23179 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d23179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d23179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d208033 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d240 q = 1) (hb : d208033 q = 1) : d23180 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, d23180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d240, d23180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241 q = 1) (hb : d208033 q = 1) : d23181 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, d23181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d241, d23181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d242 q = 1) (hb : d208033 q = 1) : d23182 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, d23182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242, d23182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d243 q = 1) (hb : d208033 q = 1) : d23183 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, d23183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243, d23183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro56021 (p : Pattern) (ha : d4359 p = 1) (hb : d208033 p = 1) : d211108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d208033 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d208033 q = 1) : d23184 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d23184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56020 q ha hb
    | true =>
      simp only [d244, d23184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4355 q = 1) (hb : d208033 q = 1) : d211104 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d211104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4355, d211104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d208033 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d208033 q = 1) : d211105 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d211105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4356, d211105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d208033 q = 1) : d211106 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d211106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d211106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d208033 q = 1) : d211107 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d211107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d211107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d208033 q = 1) : d211108 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d211108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d211108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56022 (p : Pattern) (ha : d156 p = 1) (hb : d208033 p = 1) : d23146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d208033 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56015 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d208033 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208033 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d208033 q = 1) : d23143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d208033 q = 1) : d23144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d23144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d23144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d208033 q = 1) : d23145 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d23145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d23145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d156 q = 1) (hb : d208033 q = 1) : d23146 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, d23146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, d23146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro56023 (p : Pattern) (ha : d51643 p = 1) (hb : d208033 p = 1) : d211086 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d208033 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d208033 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d208033 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157 q = 1) (hb : d208033 q = 1) : d23147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d23147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56022 q ha hb
    | true =>
      simp only [d157, d23147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d208033 q = 1) : d211082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d211082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4335, d211082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d208033 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d208033 q = 1) : d211083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d211083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d211083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d208033 q = 1) : d211084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d211084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51641, d211084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d208033 q = 1) : d211085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d211085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51642, d211085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51643 q = 1) (hb : d208033 q = 1) : d211086 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d211086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d211086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro56024 (p : Pattern) (ha : d51646 p = 1) (hb : d208033 p = 1) : d211091 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d208033 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d208033 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d208033 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d208033 q = 1) : d23147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d23147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56022 q ha hb
    | true =>
      simp only [d157, d23147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d208033 q = 1) : d211082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d211082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4335, d211082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d208033 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d208033 q = 1) : d211083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d211083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d211083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d208033 q = 1) : d211084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d211084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51641, d211084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d208033 q = 1) : d211085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d211085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51642, d211085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d208033 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d208033 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d208033 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d204 q = 1) (hb : d208033 q = 1) : d23154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d23154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56016 q ha hb
    | true =>
      simp only [d204, d23154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4340 q = 1) (hb : d208033 q = 1) : d211087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d211087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4340, d211087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d208033 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d4341 q = 1) (hb : d208033 q = 1) : d211088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d211088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4341, d211088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51644 q = 1) (hb : d208033 q = 1) : d211089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d211089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51644, d211089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51645 q = 1) (hb : d208033 q = 1) : d211090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d211090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51645, d211090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51646 q = 1) (hb : d208033 q = 1) : d211091 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d211091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51646, d211091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro56025 (p : Pattern) (ha : d51652 p = 1) (hb : d208033 p = 1) : d211114 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d208033 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51647 q = 1) (hb : d208033 q = 1) : d211092 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d211092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56023 q ha hb
    | true =>
      simp only [d51647, d211092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56024 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d208033 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51648 q = 1) (hb : d208033 q = 1) : d211093 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d211093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51648, d211093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51649 q = 1) (hb : d208033 q = 1) : d211094 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d211094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51649, d211094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51650 q = 1) (hb : d208033 q = 1) : d211095 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d211095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51650, d211095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4350 q = 1) (hb : d208033 q = 1) : d211099 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d211099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4350, d211099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56017 q ha hb
  have h8 (q : Pattern) (ha : d4351 q = 1) (hb : d208033 q = 1) : d211100 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d211100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4351, d211100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d4352 q = 1) (hb : d208033 q = 1) : d211101 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d211101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4352, d211101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4353 q = 1) (hb : d208033 q = 1) : d211102 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d211102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4353, d211102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d51651 q = 1) (hb : d208033 q = 1) : d211103 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d211103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51651, d211103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4360 q = 1) (hb : d208033 q = 1) : d211109 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d211109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4360, d211109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56021 q ha hb
  have h13 (q : Pattern) (ha : d4361 q = 1) (hb : d208033 q = 1) : d211110 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d211110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4361, d211110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d4362 q = 1) (hb : d208033 q = 1) : d211111 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d211111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4362, d211111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d4363 q = 1) (hb : d208033 q = 1) : d211112 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d211112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4363, d211112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d4364 q = 1) (hb : d208033 q = 1) : d211113 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d211113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4364, d211113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d51652 q = 1) (hb : d208033 q = 1) : d211114 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d211114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51652, d211114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro56026 (p : Pattern) (ha : d284 p = 1) (hb : d208033 p = 1) : d23205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d208033 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d208033 q = 1) : d23147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d23147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56022 q ha hb
    | true =>
      simp only [d157, d23147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d208033 q = 1) : d23201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d23201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d23201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d208033 q = 1) : d23202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d23202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d23202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d208033 q = 1) : d23203 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d23203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d23203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d208033 q = 1) : d23204 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d23204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d23204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284 q = 1) (hb : d208033 q = 1) : d23205 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d23205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d23205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro56027 (p : Pattern) (ha : d291 p = 1) (hb : d208033 p = 1) : d23212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d208033 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d208033 q = 1) : d23147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d23147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56022 q ha hb
    | true =>
      simp only [d157, d23147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d208033 q = 1) : d23201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d23201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d23201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d208033 q = 1) : d23202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d23202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d23202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d208033 q = 1) : d23203 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d23203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d23203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d208033 q = 1) : d23204 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d23204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d23204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d208033 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d204 q = 1) (hb : d208033 q = 1) : d23154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d23154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56016 q ha hb
    | true =>
      simp only [d204, d23154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287 q = 1) (hb : d208033 q = 1) : d23208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d23208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d23208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288 q = 1) (hb : d208033 q = 1) : d23209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d23209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288, d23209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d289 q = 1) (hb : d208033 q = 1) : d23210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d23210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d23210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d290 q = 1) (hb : d208033 q = 1) : d23211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d23211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d23211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d291 q = 1) (hb : d208033 q = 1) : d23212 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d23212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d291, d23212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro56028 (p : Pattern) (ha : d397 p = 1) (hb : d208033 p = 1) : d23297 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d208033 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d208033 q = 1) : d23147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d23147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56022 q ha hb
    | true =>
      simp only [d157, d23147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d208033 q = 1) : d23201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d23201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d23201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d208033 q = 1) : d23202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d23202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d23202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d208033 q = 1) : d23203 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d23203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d23203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d208033 q = 1) : d23204 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d23204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d23204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d208033 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d397 q = 1) (hb : d208033 q = 1) : d23297 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, d23297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d397, d23297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56029 (p : Pattern) (ha : d296 p = 1) (hb : d208033 p = 1) : d23217 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d208033 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56015 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d208033 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208033 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d208033 q = 1) : d23143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d208033 q = 1) : d23144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d23144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d23144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d208033 q = 1) : d23216 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d23216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d23216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d296 q = 1) (hb : d208033 q = 1) : d23217 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d296, d23217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d296, d23217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro56030 (p : Pattern) (ha : d303 p = 1) (hb : d208033 p = 1) : d23224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d208033 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56015 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d208033 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208033 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d208033 q = 1) : d23143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d208033 q = 1) : d23222 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d23222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d23222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d208033 q = 1) : d23223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d23223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d23223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d303 q = 1) (hb : d208033 q = 1) : d23224 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, d23224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, d23224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro56031 (p : Pattern) (ha : d318 p = 1) (hb : d208033 p = 1) : d23230 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d315 q = 1) : d315 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d316 q = 1) (hb : d208033 q = 1) : d23228 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d208033, d23228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316, d208033, d23228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d317 q = 1) (hb : d208033 q = 1) : d23229 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d23229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d317, d23229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d135 q = 1) : d135 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d136 q = 1) (hb : d208033 q = 1) : d5448 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d208033, d5448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d136, d208033, d5448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d137 q = 1) (hb : d208033 q = 1) : d5449 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d5449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137, d5449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d318 q = 1) (hb : d208033 q = 1) : d23230 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d318, d23230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d318, d23230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro56032 (p : Pattern) (ha : d324 p = 1) (hb : d208033 p = 1) : d23236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d208033 q = 1) : d23231 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56031 q ha hb
    | true =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d208033 q = 1) : d23232 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d208033 q = 1) : d23233 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d23233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d23233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d208033 q = 1) : d23234 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d23234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d23234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139 q = 1) (hb : d208033 q = 1) : d9382 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56013 q ha hb
    | true =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d140 q = 1) (hb : d208033 q = 1) : d9384 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d141 q = 1) (hb : d208033 q = 1) : d12493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d142 q = 1) (hb : d208033 q = 1) : d12494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d142, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d323 q = 1) (hb : d208033 q = 1) : d23235 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d23235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d323, d23235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28 q = 1) (hb : d208033 q = 1) : d28 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d143 q = 1) (hb : d208033 q = 1) : d12495 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d143, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d324 q = 1) (hb : d208033 q = 1) : d23236 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d324, d23236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d324, d23236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro56033 (p : Pattern) (ha : d330 p = 1) (hb : d208033 p = 1) : d23242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325 q = 1) (hb : d208033 q = 1) : d23237 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d23237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56032 q ha hb
    | true =>
      simp only [d325, d23237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56014 q ha hb
  have h2 (q : Pattern) (ha : d326 q = 1) (hb : d208033 q = 1) : d23238 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d23238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d23238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d327 q = 1) (hb : d208033 q = 1) : d23239 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d23239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d23239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d208033 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d208033 q = 1) : d23135 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56014 q ha hb
    | true =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d208033 q = 1) : d23136 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d208033 q = 1) : d23137 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d328 q = 1) (hb : d208033 q = 1) : d23240 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, d23240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d328, d23240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d208033 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d148 q = 1) (hb : d208033 q = 1) : d23138 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d23138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148, d23138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d329 q = 1) (hb : d208033 q = 1) : d23241 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d329, d23241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d329, d23241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d330 q = 1) (hb : d208033 q = 1) : d23242 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d330, d23242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d330, d23242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro56034 (p : Pattern) (ha : d336 p = 1) (hb : d208033 p = 1) : d23248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331 q = 1) (hb : d208033 q = 1) : d23243 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d331, d23243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56033 q ha hb
    | true =>
      simp only [d331, d23243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d332 q = 1) (hb : d208033 q = 1) : d23244 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d332, d23244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d332, d23244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d208033 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56015 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d208033 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d333 q = 1) (hb : d208033 q = 1) : d23245 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333, d23245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333, d23245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d334 q = 1) (hb : d208033 q = 1) : d23246 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334, d23246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d334, d23246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d335 q = 1) (hb : d208033 q = 1) : d23247 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335, d23247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d335, d23247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d336 q = 1) (hb : d208033 q = 1) : d23248 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336, d23248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d336, d23248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56035 (p : Pattern) (ha : d4736 p = 1) (hb : d208033 p = 1) : d23268 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d208033 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56015 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d208033 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d208033 q = 1) : d23265 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d23265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d23265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d208033 q = 1) : d23266 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d23266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d23266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d208033 q = 1) : d23267 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d23267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d23267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4736 q = 1) (hb : d208033 q = 1) : d23268 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, d23268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, d23268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56036 (p : Pattern) (ha : d74579 p = 1) (hb : d208033 p = 1) : d211124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d208033 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d208033 q = 1) : d23218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d23218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56029 q ha hb
    | true =>
      simp only [d297, d23218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d208033 q = 1) : d23219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d23219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d23219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d208033 q = 1) : d23220 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d23220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d23220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d208033 q = 1) : d23221 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d23221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d23221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d208033 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d208033 q = 1) : d23225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d23225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56030 q ha hb
    | true =>
      simp only [d304, d23225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d208033 q = 1) : d23226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d23226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d23226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d208033 q = 1) : d23227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d23227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d23227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d337 q = 1) (hb : d208033 q = 1) : d23249 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d23249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56034 q ha hb
    | true =>
      simp only [d337, d23249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56022 q ha hb
  have h11 (q : Pattern) (ha : d4371 q = 1) (hb : d208033 q = 1) : d211120 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d211120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4371, d211120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d208033 q = 1) : d23269 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d23269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56035 q ha hb
    | true =>
      simp only [d4737, d23269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d208033 q = 1) : d23270 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d23270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d23270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d74576 q = 1) (hb : d208033 q = 1) : d211121 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74576, d211121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74576, d211121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74577 q = 1) (hb : d208033 q = 1) : d211122 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74577, d211122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74577, d211122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74578 q = 1) (hb : d208033 q = 1) : d211123 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74578, d211123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74578, d211123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74579 q = 1) (hb : d208033 q = 1) : d211124 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74579, d211124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74579, d211124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro56037 (p : Pattern) (ha : d376 p = 1) (hb : d208033 p = 1) : d23275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d208033 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56015 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d208033 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208033 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d208033 q = 1) : d23143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d208033 q = 1) : d23144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d23144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d23144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d208033 q = 1) : d23216 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d23216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d23216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d376 q = 1) (hb : d208033 q = 1) : d23275 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376, d23275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d376, d23275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro56038 (p : Pattern) (ha : d381 p = 1) (hb : d208033 p = 1) : d23280 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d208033 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56015 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d208033 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d208033 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d208033 q = 1) : d23143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d23143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d208033 q = 1) : d23222 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d23222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d23222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d208033 q = 1) : d23223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d23223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d23223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d381 q = 1) (hb : d208033 q = 1) : d23280 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d381, d23280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d381, d23280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro56039 (p : Pattern) (ha : d385 p = 1) (hb : d208033 p = 1) : d23284 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331 q = 1) (hb : d208033 q = 1) : d23243 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d331, d23243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56033 q ha hb
    | true =>
      simp only [d331, d23243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d332 q = 1) (hb : d208033 q = 1) : d23244 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d332, d23244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d332, d23244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d208033 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56015 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d208033 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d333 q = 1) (hb : d208033 q = 1) : d23245 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333, d23245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333, d23245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d334 q = 1) (hb : d208033 q = 1) : d23246 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334, d23246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d334, d23246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d335 q = 1) (hb : d208033 q = 1) : d23247 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335, d23247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d335, d23247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d385 q = 1) (hb : d208033 q = 1) : d23284 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d385, d23284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d385, d23284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56040 (p : Pattern) (ha : d5355 p = 1) (hb : d208033 p = 1) : d23289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d208033 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56015 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d208033 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d208033 q = 1) : d23265 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d23265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d23265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d208033 q = 1) : d23266 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d23266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d23266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d208033 q = 1) : d23267 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d23267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d23267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5355 q = 1) (hb : d208033 q = 1) : d23289 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d23289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5355, d23289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56041 (p : Pattern) (ha : d74583 p = 1) (hb : d208033 p = 1) : d211129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d208033 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d208033 q = 1) : d23218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d23218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56029 q ha hb
    | true =>
      simp only [d297, d23218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d208033 q = 1) : d23219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d23219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d23219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d208033 q = 1) : d23220 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d23220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d23220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d208033 q = 1) : d23221 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d23221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d23221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d208033 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d208033 q = 1) : d23225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d23225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56030 q ha hb
    | true =>
      simp only [d304, d23225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d208033 q = 1) : d23226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d23226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d23226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d208033 q = 1) : d23227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d23227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d23227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d337 q = 1) (hb : d208033 q = 1) : d23249 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d23249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56034 q ha hb
    | true =>
      simp only [d337, d23249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56022 q ha hb
  have h11 (q : Pattern) (ha : d4371 q = 1) (hb : d208033 q = 1) : d211120 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d211120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4371, d211120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d208033 q = 1) : d23269 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d23269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56035 q ha hb
    | true =>
      simp only [d4737, d23269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d208033 q = 1) : d23270 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d23270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d23270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d74576 q = 1) (hb : d208033 q = 1) : d211121 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74576, d211121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74576, d211121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74577 q = 1) (hb : d208033 q = 1) : d211122 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74577, d211122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74577, d211122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74578 q = 1) (hb : d208033 q = 1) : d211123 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74578, d211123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74578, d211123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d208033 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d377 q = 1) (hb : d208033 q = 1) : d23276 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d23276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56037 q ha hb
    | true =>
      simp only [d377, d23276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d378 q = 1) (hb : d208033 q = 1) : d23277 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d23277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d378, d23277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d379 q = 1) (hb : d208033 q = 1) : d23278 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d23278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d379, d23278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d380 q = 1) (hb : d208033 q = 1) : d23279 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d23279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d23279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d208033 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d382 q = 1) (hb : d208033 q = 1) : d23281 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d23281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56038 q ha hb
    | true =>
      simp only [d382, d23281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d383 q = 1) (hb : d208033 q = 1) : d23282 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d23282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d383, d23282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d384 q = 1) (hb : d208033 q = 1) : d23283 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d23283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d384, d23283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d386 q = 1) (hb : d208033 q = 1) : d23285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d23285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56039 q ha hb
    | true =>
      simp only [d386, d23285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56016 q ha hb
  have h27 (q : Pattern) (ha : d4376 q = 1) (hb : d208033 q = 1) : d211125 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d211125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d4376, d211125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d5356 q = 1) (hb : d208033 q = 1) : d23290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d23290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56040 q ha hb
    | true =>
      simp only [d5356, d23290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d5357 q = 1) (hb : d208033 q = 1) : d23291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d23291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d5357, d23291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d74580 q = 1) (hb : d208033 q = 1) : d211126 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74580, d211126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d74580, d211126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74581 q = 1) (hb : d208033 q = 1) : d211127 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74581, d211127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d74581, d211127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d74582 q = 1) (hb : d208033 q = 1) : d211128 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74582, d211128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74582, d211128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d74583 q = 1) (hb : d208033 q = 1) : d211129 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74583, d211129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74583, d211129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro56042 (p : Pattern) (ha : d74590 p = 1) (hb : d208033 p = 1) : d211136 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d386 q = 1) (hb : d208033 q = 1) : d23285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d23285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56039 q ha hb
    | true =>
      simp only [d386, d23285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56016 q ha hb
  have h2 (q : Pattern) (ha : d4376 q = 1) (hb : d208033 q = 1) : d211125 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d211125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4376, d211125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d208033 q = 1) : d23290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d23290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56040 q ha hb
    | true =>
      simp only [d5356, d23290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5357 q = 1) (hb : d208033 q = 1) : d23291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d23291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5357, d23291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74580 q = 1) (hb : d208033 q = 1) : d211126 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74580, d211126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74580, d211126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74588 q = 1) (hb : d208033 q = 1) : d211134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74588, d211134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74588, d211134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74589 q = 1) (hb : d208033 q = 1) : d211135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74589, d211135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74589, d211135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74590 q = 1) (hb : d208033 q = 1) : d211136 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74590, d211136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74590, d211136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56043 (p : Pattern) (ha : d417 p = 1) (hb : d208033 p = 1) : d23315 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d208033 q = 1) : d23310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d23310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d23310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56031 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d208033 q = 1) : d23231 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56031 q ha hb
    | true =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d208033 q = 1) : d23311 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d23311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d23311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d208033 q = 1) : d23232 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d208033 q = 1) : d23312 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d23312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d23312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d208033 q = 1) : d23313 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d23313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d23313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d226 q = 1) (hb : d208033 q = 1) : d12599 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d12599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d12599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56013 q ha hb
  have h8 (q : Pattern) (ha : d139 q = 1) (hb : d208033 q = 1) : d9382 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56013 q ha hb
    | true =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d227 q = 1) (hb : d208033 q = 1) : d12600 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d12600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d227, d12600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d140 q = 1) (hb : d208033 q = 1) : d9384 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d228 q = 1) (hb : d208033 q = 1) : d12601 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d12601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d228, d12601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d229 q = 1) (hb : d208033 q = 1) : d12602 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d12602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d229, d12602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d416 q = 1) (hb : d208033 q = 1) : d23314 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d23314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d416, d23314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69 q = 1) (hb : d208033 q = 1) : d69 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d230 q = 1) (hb : d208033 q = 1) : d12603 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d12603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d230, d12603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d417 q = 1) (hb : d208033 q = 1) : d23315 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d417, d23315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d417, d23315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro56044 (p : Pattern) (ha : d423 p = 1) (hb : d208033 p = 1) : d23321 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d418 q = 1) (hb : d208033 q = 1) : d23316 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d23316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56043 q ha hb
    | true =>
      simp only [d418, d23316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56018 q ha hb
  have h2 (q : Pattern) (ha : d419 q = 1) (hb : d208033 q = 1) : d23317 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d23317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d23317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d420 q = 1) (hb : d208033 q = 1) : d23318 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d23318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d23318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d208033 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d208033 q = 1) : d23172 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d23172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56018 q ha hb
    | true =>
      simp only [d232, d23172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d208033 q = 1) : d23173 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d23173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d23173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d208033 q = 1) : d23174 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d23174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d23174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d421 q = 1) (hb : d208033 q = 1) : d23319 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d23319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d421, d23319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d208033 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d235 q = 1) (hb : d208033 q = 1) : d23175 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d23175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d235, d23175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d422 q = 1) (hb : d208033 q = 1) : d23320 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d422, d23320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d422, d23320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d423 q = 1) (hb : d208033 q = 1) : d23321 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d423, d23321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d423, d23321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro56045 (p : Pattern) (ha : d429 p = 1) (hb : d208033 p = 1) : d23327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d424 q = 1) (hb : d208033 q = 1) : d23322 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d424, d23322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56044 q ha hb
    | true =>
      simp only [d424, d23322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d425 q = 1) (hb : d208033 q = 1) : d23323 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d425, d23323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d425, d23323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238 q = 1) (hb : d208033 q = 1) : d23178 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d23178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56019 q ha hb
    | true =>
      simp only [d238, d23178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239 q = 1) (hb : d208033 q = 1) : d23179 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d23179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d23179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d426 q = 1) (hb : d208033 q = 1) : d23324 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d426, d23324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d426, d23324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d427 q = 1) (hb : d208033 q = 1) : d23325 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d427, d23325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d427, d23325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d428 q = 1) (hb : d208033 q = 1) : d23326 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d428, d23326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d428, d23326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d429 q = 1) (hb : d208033 q = 1) : d23327 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d429, d23327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d429, d23327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56046 (p : Pattern) (ha : d5377 p = 1) (hb : d208033 p = 1) : d23347 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d208033 q = 1) : d23178 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d23178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56019 q ha hb
    | true =>
      simp only [d238, d23178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d208033 q = 1) : d23179 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d23179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d23179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5374 q = 1) (hb : d208033 q = 1) : d23344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, d23344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, d23344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5375 q = 1) (hb : d208033 q = 1) : d23345 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, d23345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5375, d23345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5376 q = 1) (hb : d208033 q = 1) : d23346 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, d23346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5376, d23346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5377 q = 1) (hb : d208033 q = 1) : d23347 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, d23347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5377, d23347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56047 (p : Pattern) (ha : d74599 p = 1) (hb : d208033 p = 1) : d211146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d430 q = 1) (hb : d208033 q = 1) : d23328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d430, d23328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56045 q ha hb
    | true =>
      simp only [d430, d23328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56020 q ha hb
  have h2 (q : Pattern) (ha : d4391 q = 1) (hb : d208033 q = 1) : d211142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4391, d211142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4391, d211142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d208033 q = 1) : d23348 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d23348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56046 q ha hb
    | true =>
      simp only [d5378, d23348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d208033 q = 1) : d23349 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d23349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5379, d23349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74596 q = 1) (hb : d208033 q = 1) : d211143 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74596, d211143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74596, d211143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74597 q = 1) (hb : d208033 q = 1) : d211144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74597, d211144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74597, d211144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74598 q = 1) (hb : d208033 q = 1) : d211145 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74598, d211145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74598, d211145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74599 q = 1) (hb : d208033 q = 1) : d211146 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74599, d211146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74599, d211146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56048 (p : Pattern) (ha : d74605 p = 1) (hb : d208033 p = 1) : d211152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d208033 q = 1) : d23206 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d23206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d23206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56026 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d208033 q = 1) : d23207 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d23207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d23207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d208033 q = 1) : d23213 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d23213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56026 q ha hb
    | true =>
      simp only [d292, d23213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56027 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d208033 q = 1) : d23214 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d23214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d23214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d208033 q = 1) : d23215 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d23215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d23215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74584 q = 1) (hb : d208033 q = 1) : d211130 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74584, d211130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56036 q ha hb
    | true =>
      simp only [d74584, d211130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56041 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d208033 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d398 q = 1) (hb : d208033 q = 1) : d23298 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d23298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56028 q ha hb
    | true =>
      simp only [d398, d23298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74585 q = 1) (hb : d208033 q = 1) : d211131 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74585, d211131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74585, d211131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74586 q = 1) (hb : d208033 q = 1) : d211132 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74586, d211132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74586, d211132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d74587 q = 1) (hb : d208033 q = 1) : d211133 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74587, d211133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74587, d211133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d74591 q = 1) (hb : d208033 q = 1) : d211137 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74591, d211137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74591, d211137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56042 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d208033 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d74592 q = 1) (hb : d208033 q = 1) : d211138 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74592, d211138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74592, d211138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74593 q = 1) (hb : d208033 q = 1) : d211139 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74593, d211139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74593, d211139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d74594 q = 1) (hb : d208033 q = 1) : d211140 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74594, d211140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74594, d211140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d74595 q = 1) (hb : d208033 q = 1) : d211141 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74595, d211141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74595, d211141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d74600 q = 1) (hb : d208033 q = 1) : d211147 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74600, d211147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74600, d211147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56047 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d208033 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d74601 q = 1) (hb : d208033 q = 1) : d211148 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74601, d211148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74601, d211148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d74602 q = 1) (hb : d208033 q = 1) : d211149 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74602, d211149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74602, d211149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d74603 q = 1) (hb : d208033 q = 1) : d211150 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74603, d211150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74603, d211150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d74604 q = 1) (hb : d208033 q = 1) : d211151 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74604, d211151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d74604, d211151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d74605 q = 1) (hb : d208033 q = 1) : d211152 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74605, d211152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74605, d211152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro56049 (p : Pattern) (ha : d74611 p = 1) (hb : d208033 p = 1) : d211158 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d208033 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d208033 q = 1) : d211115 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d211115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d211115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56025 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d208033 q = 1) : d211116 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d211116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d211116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d208033 q = 1) : d211117 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d211117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d211117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d208033 q = 1) : d211118 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d211118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d211118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d208033 q = 1) : d211119 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d211119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51657, d211119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74606 q = 1) (hb : d208033 q = 1) : d211153 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74606, d211153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74606, d211153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56048 q ha hb
  have h8 (q : Pattern) (ha : d74607 q = 1) (hb : d208033 q = 1) : d211154 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74607, d211154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74607, d211154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74608 q = 1) (hb : d208033 q = 1) : d211155 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74608, d211155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74608, d211155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74609 q = 1) (hb : d208033 q = 1) : d211156 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74609, d211156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74609, d211156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74610 q = 1) (hb : d208033 q = 1) : d211157 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74610, d211157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74610, d211157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d74611 q = 1) (hb : d208033 q = 1) : d211158 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74611, d211158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74611, d211158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro56050 (p : Pattern) (ha : d477 p = 1) (hb : d208033 p = 1) : d23368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325 q = 1) (hb : d208033 q = 1) : d23237 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d23237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56032 q ha hb
    | true =>
      simp only [d325, d23237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56014 q ha hb
  have h2 (q : Pattern) (ha : d326 q = 1) (hb : d208033 q = 1) : d23238 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d23238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d23238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d327 q = 1) (hb : d208033 q = 1) : d23239 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d23239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d23239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d208033 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d208033 q = 1) : d23135 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56014 q ha hb
    | true =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d208033 q = 1) : d23136 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d208033 q = 1) : d23137 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d328 q = 1) (hb : d208033 q = 1) : d23240 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, d23240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d328, d23240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d475 q = 1) (hb : d208033 q = 1) : d23366 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d23366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d475, d23366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d476 q = 1) (hb : d208033 q = 1) : d23367 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d476, d23367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d476, d23367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d477 q = 1) (hb : d208033 q = 1) : d23368 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d477, d23368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d477, d23368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro56051 (p : Pattern) (ha : d481 p = 1) (hb : d208033 p = 1) : d23372 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d208033 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d208033 q = 1) : d23135 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56014 q ha hb
    | true =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d208033 q = 1) : d23136 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d208033 q = 1) : d23137 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d475 q = 1) (hb : d208033 q = 1) : d23366 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d23366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d475, d23366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d480 q = 1) (hb : d208033 q = 1) : d23371 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d23371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d480, d23371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d481 q = 1) (hb : d208033 q = 1) : d23372 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d23372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d481, d23372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro56052 (p : Pattern) (ha : d487 p = 1) (hb : d208033 p = 1) : d23378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d208033 q = 1) : d23369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56050 q ha hb
    | true =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d208033 q = 1) : d23370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d208033 q = 1) : d23373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56051 q ha hb
    | true =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d208033 q = 1) : d23374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d484 q = 1) (hb : d208033 q = 1) : d23375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d485 q = 1) (hb : d208033 q = 1) : d23376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d23376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d485, d23376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d486 q = 1) (hb : d208033 q = 1) : d23377 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d486, d23377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d486, d23377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d487 q = 1) (hb : d208033 q = 1) : d23378 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d487, d23378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d487, d23378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56053 (p : Pattern) (ha : d491 p = 1) (hb : d208033 p = 1) : d23382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d208033 q = 1) : d23373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56051 q ha hb
    | true =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d208033 q = 1) : d23374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d208033 q = 1) : d23379 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d23379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d23379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d208033 q = 1) : d23380 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d23380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d23380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d208033 q = 1) : d23381 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d23381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d23381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d208033 q = 1) : d23382 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d23382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d23382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56054 (p : Pattern) (ha : d497 p = 1) (hb : d208033 p = 1) : d23388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d492 q = 1) (hb : d208033 q = 1) : d23383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d23383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56052 q ha hb
    | true =>
      simp only [d492, d23383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56053 q ha hb
  have h2 (q : Pattern) (ha : d493 q = 1) (hb : d208033 q = 1) : d23384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d23384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d493, d23384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d494 q = 1) (hb : d208033 q = 1) : d23385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d23385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d494, d23385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d495 q = 1) (hb : d208033 q = 1) : d23386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d23386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, d23386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d496 q = 1) (hb : d208033 q = 1) : d23387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d23387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d23387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d497 q = 1) (hb : d208033 q = 1) : d23388 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d497, d23388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d497, d23388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56055 (p : Pattern) (ha : d500 p = 1) (hb : d208033 p = 1) : d23391 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d208033 q = 1) : d23369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56050 q ha hb
    | true =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d208033 q = 1) : d23370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d208033 q = 1) : d23373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56051 q ha hb
    | true =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d208033 q = 1) : d23374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d484 q = 1) (hb : d208033 q = 1) : d23375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d485 q = 1) (hb : d208033 q = 1) : d23376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d23376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d485, d23376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d486 q = 1) (hb : d208033 q = 1) : d23377 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d486, d23377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d486, d23377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d500 q = 1) (hb : d208033 q = 1) : d23391 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d500, d23391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d500, d23391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56056 (p : Pattern) (ha : d501 p = 1) (hb : d208033 p = 1) : d23392 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d208033 q = 1) : d23373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56051 q ha hb
    | true =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d208033 q = 1) : d23374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d208033 q = 1) : d23379 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d23379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d23379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d208033 q = 1) : d23380 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d23380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d23380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d208033 q = 1) : d23381 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d23381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d23381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d208033 q = 1) : d23392 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d23392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d23392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56057 (p : Pattern) (ha : d507 p = 1) (hb : d208033 p = 1) : d23398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d492 q = 1) (hb : d208033 q = 1) : d23383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d23383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56052 q ha hb
    | true =>
      simp only [d492, d23383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56053 q ha hb
  have h2 (q : Pattern) (ha : d493 q = 1) (hb : d208033 q = 1) : d23384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d23384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d493, d23384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d494 q = 1) (hb : d208033 q = 1) : d23385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d23385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d494, d23385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d495 q = 1) (hb : d208033 q = 1) : d23386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d23386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, d23386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d496 q = 1) (hb : d208033 q = 1) : d23387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d23387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d23387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d502 q = 1) (hb : d208033 q = 1) : d23393 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, d23393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56055 q ha hb
    | true =>
      simp only [d502, d23393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56056 q ha hb
  have h7 (q : Pattern) (ha : d503 q = 1) (hb : d208033 q = 1) : d23394 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d23394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d503, d23394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d504 q = 1) (hb : d208033 q = 1) : d23395 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d23395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d504, d23395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d505 q = 1) (hb : d208033 q = 1) : d23396 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d23396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, d23396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d506 q = 1) (hb : d208033 q = 1) : d23397 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d23397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, d23397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d507 q = 1) (hb : d208033 q = 1) : d23398 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d507, d23398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d507, d23398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56058 (p : Pattern) (ha : d638 p = 1) (hb : d208033 p = 1) : d23513 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d492 q = 1) (hb : d208033 q = 1) : d23383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d23383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56052 q ha hb
    | true =>
      simp only [d492, d23383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56053 q ha hb
  have h2 (q : Pattern) (ha : d493 q = 1) (hb : d208033 q = 1) : d23384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d23384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d493, d23384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d494 q = 1) (hb : d208033 q = 1) : d23385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d23385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d494, d23385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d495 q = 1) (hb : d208033 q = 1) : d23386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d23386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, d23386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d496 q = 1) (hb : d208033 q = 1) : d23387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d23387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d23387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d208033 q = 1) : d23508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d23508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56053 q ha hb
    | true =>
      simp only [d633, d23508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d208033 q = 1) : d23509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d23509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d23509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d208033 q = 1) : d23510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d23510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d23510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d208033 q = 1) : d23511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d23511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d23511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d208033 q = 1) : d23512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d23512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d23512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d638 q = 1) (hb : d208033 q = 1) : d23513 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d638, d23513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d638, d23513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56059 (p : Pattern) (ha : d644 p = 1) (hb : d208033 p = 1) : d23519 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d208033 q = 1) : d23508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d23508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56053 q ha hb
    | true =>
      simp only [d633, d23508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d208033 q = 1) : d23509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d23509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d23509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d208033 q = 1) : d23510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d23510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, d23510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d208033 q = 1) : d23511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d23511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d23511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d208033 q = 1) : d23512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d23512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d23512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d639 q = 1) (hb : d208033 q = 1) : d23514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d23514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56056 q ha hb
    | true =>
      simp only [d639, d23514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d640 q = 1) (hb : d208033 q = 1) : d23515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d23515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d23515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d641 q = 1) (hb : d208033 q = 1) : d23516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d23516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d641, d23516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d642 q = 1) (hb : d208033 q = 1) : d23517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d23517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d23517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d643 q = 1) (hb : d208033 q = 1) : d23518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d23518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d23518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d644 q = 1) (hb : d208033 q = 1) : d23519 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, d23519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d644, d23519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56060 (p : Pattern) (ha : d653 p = 1) (hb : d208033 p = 1) : d23528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d208033 q = 1) : d23514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d23514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56056 q ha hb
    | true =>
      simp only [d639, d23514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d208033 q = 1) : d23515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d23515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d23515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d208033 q = 1) : d23516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d23516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, d23516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d208033 q = 1) : d23517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d23517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d23517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d208033 q = 1) : d23518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d23518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d23518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d208033 q = 1) : d23528 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, d23528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, d23528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56061 (p : Pattern) (ha : d683 p = 1) (hb : d208033 p = 1) : d23558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d208033 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d208033 q = 1) : d23172 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d23172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56018 q ha hb
    | true =>
      simp only [d232, d23172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d208033 q = 1) : d23173 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d23173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d23173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d208033 q = 1) : d23174 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d23174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d23174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d673 q = 1) (hb : d208033 q = 1) : d23548 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d23548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d673, d23548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d682 q = 1) (hb : d208033 q = 1) : d23557 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d23557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d682, d23557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d683 q = 1) (hb : d208033 q = 1) : d23558 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d23558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d683, d23558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro56062 (p : Pattern) (ha : d730 p = 1) (hb : d208033 p = 1) : d23609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d208033 q = 1) : d23559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d23559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56061 q ha hb
    | true =>
      simp only [d684, d23559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d208033 q = 1) : d23560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d23560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d23560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d208033 q = 1) : d23606 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d23606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d23606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d208033 q = 1) : d23607 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d23607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d23607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d208033 q = 1) : d23608 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d23608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d23608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d208033 q = 1) : d23609 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d23609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d23609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56063 (p : Pattern) (ha : d736 p = 1) (hb : d208033 p = 1) : d23615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d208033 q = 1) : d23610 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d23610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56062 q ha hb
    | true =>
      simp only [d731, d23610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d208033 q = 1) : d23611 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d23611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, d23611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d208033 q = 1) : d23612 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d23612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, d23612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d208033 q = 1) : d23613 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, d23613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, d23613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d208033 q = 1) : d23614 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, d23614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, d23614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d208033 q = 1) : d23615 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, d23615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, d23615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56064 (p : Pattern) (ha : d512 p = 1) (hb : d208033 p = 1) : d23403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d208033 q = 1) : d23369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56050 q ha hb
    | true =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d208033 q = 1) : d23370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d208033 q = 1) : d23373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56051 q ha hb
    | true =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d208033 q = 1) : d23374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d484 q = 1) (hb : d208033 q = 1) : d23375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d485 q = 1) (hb : d208033 q = 1) : d23376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d23376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d485, d23376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d511 q = 1) (hb : d208033 q = 1) : d23402 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d511, d23402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d511, d23402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d512 q = 1) (hb : d208033 q = 1) : d23403 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d512, d23403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d512, d23403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56065 (p : Pattern) (ha : d514 p = 1) (hb : d208033 p = 1) : d23405 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d208033 q = 1) : d23373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56051 q ha hb
    | true =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d208033 q = 1) : d23374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d208033 q = 1) : d23379 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d23379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d23379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d208033 q = 1) : d23380 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d23380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d23380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d208033 q = 1) : d23404 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d23404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d23404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d514 q = 1) (hb : d208033 q = 1) : d23405 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, d23405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, d23405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56066 (p : Pattern) (ha : d521 p = 1) (hb : d208033 p = 1) : d23412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d208033 q = 1) : d23369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56050 q ha hb
    | true =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d208033 q = 1) : d23370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d208033 q = 1) : d23373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56051 q ha hb
    | true =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d208033 q = 1) : d23374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d484 q = 1) (hb : d208033 q = 1) : d23375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d519 q = 1) (hb : d208033 q = 1) : d23410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d519, d23410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d519, d23410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d520 q = 1) (hb : d208033 q = 1) : d23411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d520, d23411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d520, d23411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d521 q = 1) (hb : d208033 q = 1) : d23412 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d521, d23412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d521, d23412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56067 (p : Pattern) (ha : d524 p = 1) (hb : d208033 p = 1) : d23415 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d208033 q = 1) : d23373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56051 q ha hb
    | true =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d208033 q = 1) : d23374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d208033 q = 1) : d23379 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d23379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d23379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d208033 q = 1) : d23413 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d23413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d23413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d208033 q = 1) : d23414 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d23414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d23414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d208033 q = 1) : d23415 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, d23415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, d23415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56068 (p : Pattern) (ha : d542 p = 1) (hb : d208033 p = 1) : d23421 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d533 q = 1) : d533 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d539 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d540 q = 1) (hb : d208033 q = 1) : d23419 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d540, d208033, d23419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d540, d208033, d23419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d541 q = 1) (hb : d208033 q = 1) : d23420 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d541, d23420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d541, d23420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d315 q = 1) : d315 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d135 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d316 q = 1) (hb : d208033 q = 1) : d23228 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d208033, d23228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d316, d208033, d23228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d317 q = 1) (hb : d208033 q = 1) : d23229 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d23229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d317, d23229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d542 q = 1) (hb : d208033 q = 1) : d23421 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d542, d23421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d542, d23421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro56069 (p : Pattern) (ha : d548 p = 1) (hb : d208033 p = 1) : d23427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d208033 q = 1) : d23422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56068 q ha hb
    | true =>
      simp only [d543, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d208033 q = 1) : d23423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d208033 q = 1) : d23424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d23424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d23424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d208033 q = 1) : d23425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d23425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d23425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d319 q = 1) (hb : d208033 q = 1) : d23231 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56031 q ha hb
    | true =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d320 q = 1) (hb : d208033 q = 1) : d23232 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d321 q = 1) (hb : d208033 q = 1) : d23233 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d23233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d23233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322 q = 1) (hb : d208033 q = 1) : d23234 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d23234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d322, d23234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d547 q = 1) (hb : d208033 q = 1) : d23426 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d547, d23426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d547, d23426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d139 q = 1) (hb : d208033 q = 1) : d9382 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56013 q ha hb
    | true =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d140 q = 1) (hb : d208033 q = 1) : d9384 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d141 q = 1) (hb : d208033 q = 1) : d12493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d142 q = 1) (hb : d208033 q = 1) : d12494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d142, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d323 q = 1) (hb : d208033 q = 1) : d23235 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d23235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d323, d23235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d548 q = 1) (hb : d208033 q = 1) : d23427 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d548, d23427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d548, d23427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56070 (p : Pattern) (ha : d554 p = 1) (hb : d208033 p = 1) : d23433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d549 q = 1) (hb : d208033 q = 1) : d23428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d549, d23428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56069 q ha hb
    | true =>
      simp only [d549, d23428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56032 q ha hb
  have h2 (q : Pattern) (ha : d550 q = 1) (hb : d208033 q = 1) : d23429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d550, d23429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d550, d23429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d551 q = 1) (hb : d208033 q = 1) : d23430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d551, d23430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d551, d23430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d325 q = 1) (hb : d208033 q = 1) : d23237 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d23237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56032 q ha hb
    | true =>
      simp only [d325, d23237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56014 q ha hb
  have h5 (q : Pattern) (ha : d326 q = 1) (hb : d208033 q = 1) : d23238 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d23238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d23238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d327 q = 1) (hb : d208033 q = 1) : d23239 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d23239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d23239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d552 q = 1) (hb : d208033 q = 1) : d23431 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d552, d23431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d552, d23431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30 q = 1) (hb : d208033 q = 1) : d30 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d145 q = 1) (hb : d208033 q = 1) : d23135 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56014 q ha hb
    | true =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146 q = 1) (hb : d208033 q = 1) : d23136 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147 q = 1) (hb : d208033 q = 1) : d23137 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d328 q = 1) (hb : d208033 q = 1) : d23240 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, d23240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d328, d23240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d553 q = 1) (hb : d208033 q = 1) : d23432 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d553, d23432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d553, d23432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d554 q = 1) (hb : d208033 q = 1) : d23433 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d554, d23433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d554, d23433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro56071 (p : Pattern) (ha : d560 p = 1) (hb : d208033 p = 1) : d23439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d555 q = 1) (hb : d208033 q = 1) : d23434 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d555, d23434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56070 q ha hb
    | true =>
      simp only [d555, d23434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d556 q = 1) (hb : d208033 q = 1) : d23435 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d556, d23435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d556, d23435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d478 q = 1) (hb : d208033 q = 1) : d23369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56050 q ha hb
    | true =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d479 q = 1) (hb : d208033 q = 1) : d23370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d557 q = 1) (hb : d208033 q = 1) : d23436 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d557, d23436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d557, d23436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d558 q = 1) (hb : d208033 q = 1) : d23437 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d558, d23437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d558, d23437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d559 q = 1) (hb : d208033 q = 1) : d23438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d559, d23438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d559, d23438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d560 q = 1) (hb : d208033 q = 1) : d23439 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d560, d23439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d560, d23439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56072 (p : Pattern) (ha : d5399 p = 1) (hb : d208033 p = 1) : d23476 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d208033 q = 1) : d23369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56050 q ha hb
    | true =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d208033 q = 1) : d23370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5396 q = 1) (hb : d208033 q = 1) : d23473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d23473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5396, d23473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5397 q = 1) (hb : d208033 q = 1) : d23474 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5397, d23474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5397, d23474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5398 q = 1) (hb : d208033 q = 1) : d23475 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5398, d23475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5398, d23475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5399 q = 1) (hb : d208033 q = 1) : d23476 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5399, d23476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5399, d23476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56073 (p : Pattern) (ha : d74615 p = 1) (hb : d208033 p = 1) : d211163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d515 q = 1) (hb : d208033 q = 1) : d23406 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, d23406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56064 q ha hb
    | true =>
      simp only [d515, d23406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56065 q ha hb
  have h2 (q : Pattern) (ha : d516 q = 1) (hb : d208033 q = 1) : d23407 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d23407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d516, d23407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d517 q = 1) (hb : d208033 q = 1) : d23408 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d23408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d517, d23408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d518 q = 1) (hb : d208033 q = 1) : d23409 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d23409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, d23409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d525 q = 1) (hb : d208033 q = 1) : d23416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d23416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56066 q ha hb
    | true =>
      simp only [d525, d23416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56067 q ha hb
  have h6 (q : Pattern) (ha : d526 q = 1) (hb : d208033 q = 1) : d23417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d23417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d526, d23417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d527 q = 1) (hb : d208033 q = 1) : d23418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d23418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d527, d23418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d561 q = 1) (hb : d208033 q = 1) : d23440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d23440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56071 q ha hb
    | true =>
      simp only [d561, d23440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56052 q ha hb
  have h9 (q : Pattern) (ha : d4408 q = 1) (hb : d208033 q = 1) : d211159 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d211159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4408, d211159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5400 q = 1) (hb : d208033 q = 1) : d23477 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d23477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56072 q ha hb
    | true =>
      simp only [d5400, d23477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5401 q = 1) (hb : d208033 q = 1) : d23478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5401, d23478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5401, d23478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74612 q = 1) (hb : d208033 q = 1) : d211160 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74612, d211160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74612, d211160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74613 q = 1) (hb : d208033 q = 1) : d211161 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74613, d211161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74613, d211161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74614 q = 1) (hb : d208033 q = 1) : d211162 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74614, d211162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74614, d211162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74615 q = 1) (hb : d208033 q = 1) : d211163 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74615, d211163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74615, d211163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56074 (p : Pattern) (ha : d609 p = 1) (hb : d208033 p = 1) : d23483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d208033 q = 1) : d23369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56050 q ha hb
    | true =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d208033 q = 1) : d23370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d208033 q = 1) : d23373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56051 q ha hb
    | true =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d208033 q = 1) : d23374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d484 q = 1) (hb : d208033 q = 1) : d23375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d485 q = 1) (hb : d208033 q = 1) : d23376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d23376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d485, d23376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d511 q = 1) (hb : d208033 q = 1) : d23402 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d511, d23402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d511, d23402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d609 q = 1) (hb : d208033 q = 1) : d23483 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d609, d23483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d609, d23483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56075 (p : Pattern) (ha : d610 p = 1) (hb : d208033 p = 1) : d23484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d208033 q = 1) : d23373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56051 q ha hb
    | true =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d208033 q = 1) : d23374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d208033 q = 1) : d23379 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d23379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d23379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d208033 q = 1) : d23380 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d23380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d23380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d208033 q = 1) : d23404 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d23404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d23404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d610 q = 1) (hb : d208033 q = 1) : d23484 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, d23484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d610, d23484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56076 (p : Pattern) (ha : d615 p = 1) (hb : d208033 p = 1) : d23489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d208033 q = 1) : d23369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56050 q ha hb
    | true =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d208033 q = 1) : d23370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d208033 q = 1) : d23373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56051 q ha hb
    | true =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d208033 q = 1) : d23374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d484 q = 1) (hb : d208033 q = 1) : d23375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d519 q = 1) (hb : d208033 q = 1) : d23410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d519, d23410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d519, d23410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d520 q = 1) (hb : d208033 q = 1) : d23411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d520, d23411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d520, d23411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d615 q = 1) (hb : d208033 q = 1) : d23489 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d615, d23489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d615, d23489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56077 (p : Pattern) (ha : d616 p = 1) (hb : d208033 p = 1) : d23490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d208033 q = 1) : d23373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56051 q ha hb
    | true =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d208033 q = 1) : d23374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d208033 q = 1) : d23379 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d23379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d23379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d208033 q = 1) : d23413 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d23413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d23413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d208033 q = 1) : d23414 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d23414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d23414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d616 q = 1) (hb : d208033 q = 1) : d23490 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, d23490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d616, d23490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56078 (p : Pattern) (ha : d620 p = 1) (hb : d208033 p = 1) : d23494 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d555 q = 1) (hb : d208033 q = 1) : d23434 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d555, d23434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56070 q ha hb
    | true =>
      simp only [d555, d23434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d556 q = 1) (hb : d208033 q = 1) : d23435 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d556, d23435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d556, d23435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d478 q = 1) (hb : d208033 q = 1) : d23369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56050 q ha hb
    | true =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d479 q = 1) (hb : d208033 q = 1) : d23370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d557 q = 1) (hb : d208033 q = 1) : d23436 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d557, d23436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d557, d23436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d558 q = 1) (hb : d208033 q = 1) : d23437 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d558, d23437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d558, d23437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d559 q = 1) (hb : d208033 q = 1) : d23438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d559, d23438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d559, d23438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d620 q = 1) (hb : d208033 q = 1) : d23494 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d620, d23494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d620, d23494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56079 (p : Pattern) (ha : d5406 p = 1) (hb : d208033 p = 1) : d23500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d208033 q = 1) : d23369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56050 q ha hb
    | true =>
      simp only [d478, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d208033 q = 1) : d23370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5396 q = 1) (hb : d208033 q = 1) : d23473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d23473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5396, d23473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5397 q = 1) (hb : d208033 q = 1) : d23474 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5397, d23474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5397, d23474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5398 q = 1) (hb : d208033 q = 1) : d23475 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5398, d23475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5398, d23475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5406 q = 1) (hb : d208033 q = 1) : d23500 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5406, d23500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5406, d23500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56080 (p : Pattern) (ha : d74619 p = 1) (hb : d208033 p = 1) : d211168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d515 q = 1) (hb : d208033 q = 1) : d23406 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, d23406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56064 q ha hb
    | true =>
      simp only [d515, d23406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56065 q ha hb
  have h2 (q : Pattern) (ha : d516 q = 1) (hb : d208033 q = 1) : d23407 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d23407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d516, d23407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d517 q = 1) (hb : d208033 q = 1) : d23408 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d23408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d517, d23408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d518 q = 1) (hb : d208033 q = 1) : d23409 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d23409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, d23409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d525 q = 1) (hb : d208033 q = 1) : d23416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d23416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56066 q ha hb
    | true =>
      simp only [d525, d23416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56067 q ha hb
  have h6 (q : Pattern) (ha : d526 q = 1) (hb : d208033 q = 1) : d23417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d23417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d526, d23417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d527 q = 1) (hb : d208033 q = 1) : d23418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d23418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d527, d23418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d561 q = 1) (hb : d208033 q = 1) : d23440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d23440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56071 q ha hb
    | true =>
      simp only [d561, d23440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56052 q ha hb
  have h9 (q : Pattern) (ha : d4408 q = 1) (hb : d208033 q = 1) : d211159 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d211159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4408, d211159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5400 q = 1) (hb : d208033 q = 1) : d23477 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d23477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56072 q ha hb
    | true =>
      simp only [d5400, d23477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5401 q = 1) (hb : d208033 q = 1) : d23478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5401, d23478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5401, d23478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74612 q = 1) (hb : d208033 q = 1) : d211160 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74612, d211160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74612, d211160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74613 q = 1) (hb : d208033 q = 1) : d211161 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74613, d211161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74613, d211161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74614 q = 1) (hb : d208033 q = 1) : d211162 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74614, d211162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74614, d211162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d611 q = 1) (hb : d208033 q = 1) : d23485 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d611, d23485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56074 q ha hb
    | true =>
      simp only [d611, d23485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56075 q ha hb
  have h16 (q : Pattern) (ha : d612 q = 1) (hb : d208033 q = 1) : d23486 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d612, d23486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d612, d23486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d613 q = 1) (hb : d208033 q = 1) : d23487 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d613, d23487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d613, d23487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d614 q = 1) (hb : d208033 q = 1) : d23488 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d614, d23488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d614, d23488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d617 q = 1) (hb : d208033 q = 1) : d23491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d617, d23491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56076 q ha hb
    | true =>
      simp only [d617, d23491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56077 q ha hb
  have h20 (q : Pattern) (ha : d618 q = 1) (hb : d208033 q = 1) : d23492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d618, d23492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d618, d23492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d619 q = 1) (hb : d208033 q = 1) : d23493 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d619, d23493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d619, d23493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d621 q = 1) (hb : d208033 q = 1) : d23495 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d23495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56078 q ha hb
    | true =>
      simp only [d621, d23495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56055 q ha hb
  have h23 (q : Pattern) (ha : d4413 q = 1) (hb : d208033 q = 1) : d211164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d211164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4413, d211164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d5407 q = 1) (hb : d208033 q = 1) : d23501 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d23501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56079 q ha hb
    | true =>
      simp only [d5407, d23501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d5408 q = 1) (hb : d208033 q = 1) : d23502 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5408, d23502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5408, d23502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d74616 q = 1) (hb : d208033 q = 1) : d211165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74616, d211165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d74616, d211165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d74617 q = 1) (hb : d208033 q = 1) : d211166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74617, d211166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74617, d211166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d74618 q = 1) (hb : d208033 q = 1) : d211167 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74618, d211167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74618, d211167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d74619 q = 1) (hb : d208033 q = 1) : d211168 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74619, d211168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74619, d211168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro56081 (p : Pattern) (ha : d74626 p = 1) (hb : d208033 p = 1) : d211175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d621 q = 1) (hb : d208033 q = 1) : d23495 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d23495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56078 q ha hb
    | true =>
      simp only [d621, d23495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56055 q ha hb
  have h2 (q : Pattern) (ha : d4413 q = 1) (hb : d208033 q = 1) : d211164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d211164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4413, d211164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5407 q = 1) (hb : d208033 q = 1) : d23501 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d23501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56079 q ha hb
    | true =>
      simp only [d5407, d23501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5408 q = 1) (hb : d208033 q = 1) : d23502 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5408, d23502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5408, d23502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74616 q = 1) (hb : d208033 q = 1) : d211165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74616, d211165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74616, d211165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74624 q = 1) (hb : d208033 q = 1) : d211173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74624, d211173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74624, d211173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74625 q = 1) (hb : d208033 q = 1) : d211174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74625, d211174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74625, d211174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74626 q = 1) (hb : d208033 q = 1) : d211175 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74626, d211175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74626, d211175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56082 (p : Pattern) (ha : d664 p = 1) (hb : d208033 p = 1) : d23539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d208033 q = 1) : d23534 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d23534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d23534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56068 q ha hb
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d208033 q = 1) : d23422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56068 q ha hb
    | true =>
      simp only [d543, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d660 q = 1) (hb : d208033 q = 1) : d23535 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d23535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d660, d23535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d544 q = 1) (hb : d208033 q = 1) : d23423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d661 q = 1) (hb : d208033 q = 1) : d23536 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d23536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d661, d23536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d662 q = 1) (hb : d208033 q = 1) : d23537 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d23537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d662, d23537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d412 q = 1) (hb : d208033 q = 1) : d23310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d23310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d23310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56031 q ha hb
  have h8 (q : Pattern) (ha : d319 q = 1) (hb : d208033 q = 1) : d23231 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56031 q ha hb
    | true =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d413 q = 1) (hb : d208033 q = 1) : d23311 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d23311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d413, d23311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320 q = 1) (hb : d208033 q = 1) : d23232 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d414 q = 1) (hb : d208033 q = 1) : d23312 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d23312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d414, d23312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d415 q = 1) (hb : d208033 q = 1) : d23313 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d23313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d415, d23313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d663 q = 1) (hb : d208033 q = 1) : d23538 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d663, d23538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d663, d23538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d226 q = 1) (hb : d208033 q = 1) : d12599 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d12599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d12599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56013 q ha hb
  have h15 (q : Pattern) (ha : d139 q = 1) (hb : d208033 q = 1) : d9382 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56013 q ha hb
    | true =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d227 q = 1) (hb : d208033 q = 1) : d12600 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d12600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d227, d12600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d140 q = 1) (hb : d208033 q = 1) : d9384 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d228 q = 1) (hb : d208033 q = 1) : d12601 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d12601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d228, d12601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d229 q = 1) (hb : d208033 q = 1) : d12602 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d12602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d229, d12602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d416 q = 1) (hb : d208033 q = 1) : d23314 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d23314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d416, d23314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d664 q = 1) (hb : d208033 q = 1) : d23539 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d664, d23539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d664, d23539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro56083 (p : Pattern) (ha : d670 p = 1) (hb : d208033 p = 1) : d23545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d665 q = 1) (hb : d208033 q = 1) : d23540 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d665, d23540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56082 q ha hb
    | true =>
      simp only [d665, d23540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56043 q ha hb
  have h2 (q : Pattern) (ha : d666 q = 1) (hb : d208033 q = 1) : d23541 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d666, d23541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d666, d23541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d667 q = 1) (hb : d208033 q = 1) : d23542 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d667, d23542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d667, d23542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d418 q = 1) (hb : d208033 q = 1) : d23316 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d23316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56043 q ha hb
    | true =>
      simp only [d418, d23316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56018 q ha hb
  have h5 (q : Pattern) (ha : d419 q = 1) (hb : d208033 q = 1) : d23317 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d23317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d23317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d420 q = 1) (hb : d208033 q = 1) : d23318 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d23318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d23318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d668 q = 1) (hb : d208033 q = 1) : d23543 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d668, d23543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d668, d23543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71 q = 1) (hb : d208033 q = 1) : d71 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d232 q = 1) (hb : d208033 q = 1) : d23172 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d23172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56018 q ha hb
    | true =>
      simp only [d232, d23172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d233 q = 1) (hb : d208033 q = 1) : d23173 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d23173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d23173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d234 q = 1) (hb : d208033 q = 1) : d23174 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d23174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d23174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d421 q = 1) (hb : d208033 q = 1) : d23319 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d23319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d421, d23319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d669 q = 1) (hb : d208033 q = 1) : d23544 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d669, d23544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d669, d23544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d670 q = 1) (hb : d208033 q = 1) : d23545 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d670, d23545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d670, d23545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro56084 (p : Pattern) (ha : d675 p = 1) (hb : d208033 p = 1) : d23550 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d418 q = 1) (hb : d208033 q = 1) : d23316 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d23316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56043 q ha hb
    | true =>
      simp only [d418, d23316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56018 q ha hb
  have h2 (q : Pattern) (ha : d419 q = 1) (hb : d208033 q = 1) : d23317 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d23317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d23317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d420 q = 1) (hb : d208033 q = 1) : d23318 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d23318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d23318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d208033 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d208033 q = 1) : d23172 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d23172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56018 q ha hb
    | true =>
      simp only [d232, d23172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d208033 q = 1) : d23173 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d23173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d23173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d208033 q = 1) : d23174 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d23174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d23174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d421 q = 1) (hb : d208033 q = 1) : d23319 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d23319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d421, d23319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d673 q = 1) (hb : d208033 q = 1) : d23548 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d23548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d673, d23548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d674 q = 1) (hb : d208033 q = 1) : d23549 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d674, d23549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d674, d23549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d675 q = 1) (hb : d208033 q = 1) : d23550 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d675, d23550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d675, d23550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro56085 (p : Pattern) (ha : d681 p = 1) (hb : d208033 p = 1) : d23556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d671 q = 1) (hb : d208033 q = 1) : d23546 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d671, d23546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56083 q ha hb
    | true =>
      simp only [d671, d23546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d672 q = 1) (hb : d208033 q = 1) : d23547 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d672, d23547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d672, d23547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d676 q = 1) (hb : d208033 q = 1) : d23551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d676, d23551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56084 q ha hb
    | true =>
      simp only [d676, d23551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d677 q = 1) (hb : d208033 q = 1) : d23552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d677, d23552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d677, d23552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d678 q = 1) (hb : d208033 q = 1) : d23553 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d678, d23553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d678, d23553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d679 q = 1) (hb : d208033 q = 1) : d23554 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d679, d23554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d679, d23554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d680 q = 1) (hb : d208033 q = 1) : d23555 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d680, d23555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d680, d23555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d681 q = 1) (hb : d208033 q = 1) : d23556 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d681, d23556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d681, d23556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56086 (p : Pattern) (ha : d689 p = 1) (hb : d208033 p = 1) : d23564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d676 q = 1) (hb : d208033 q = 1) : d23551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d676, d23551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56084 q ha hb
    | true =>
      simp only [d676, d23551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d677 q = 1) (hb : d208033 q = 1) : d23552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d677, d23552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d677, d23552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d208033 q = 1) : d23559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d23559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56061 q ha hb
    | true =>
      simp only [d684, d23559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d208033 q = 1) : d23560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d23560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d23560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d686 q = 1) (hb : d208033 q = 1) : d23561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d686, d23561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d686, d23561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d687 q = 1) (hb : d208033 q = 1) : d23562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d687, d23562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d687, d23562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d688 q = 1) (hb : d208033 q = 1) : d23563 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d688, d23563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d688, d23563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d689 q = 1) (hb : d208033 q = 1) : d23564 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d689, d23564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d689, d23564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56087 (p : Pattern) (ha : d5428 p = 1) (hb : d208033 p = 1) : d23598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d676 q = 1) (hb : d208033 q = 1) : d23551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d676, d23551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56084 q ha hb
    | true =>
      simp only [d676, d23551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d677 q = 1) (hb : d208033 q = 1) : d23552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d677, d23552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d677, d23552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5425 q = 1) (hb : d208033 q = 1) : d23595 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5425, d23595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5425, d23595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5426 q = 1) (hb : d208033 q = 1) : d23596 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5426, d23596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5426, d23596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5427 q = 1) (hb : d208033 q = 1) : d23597 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5427, d23597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5427, d23597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5428 q = 1) (hb : d208033 q = 1) : d23598 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5428, d23598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5428, d23598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56088 (p : Pattern) (ha : d74635 p = 1) (hb : d208033 p = 1) : d211185 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d690 q = 1) (hb : d208033 q = 1) : d23565 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d690, d23565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56085 q ha hb
    | true =>
      simp only [d690, d23565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56086 q ha hb
  have h2 (q : Pattern) (ha : d4428 q = 1) (hb : d208033 q = 1) : d211181 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4428, d211181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4428, d211181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5429 q = 1) (hb : d208033 q = 1) : d23599 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5429, d23599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56087 q ha hb
    | true =>
      simp only [d5429, d23599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5430 q = 1) (hb : d208033 q = 1) : d23600 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5430, d23600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5430, d23600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74632 q = 1) (hb : d208033 q = 1) : d211182 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74632, d211182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74632, d211182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74633 q = 1) (hb : d208033 q = 1) : d211183 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74633, d211183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74633, d211183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74634 q = 1) (hb : d208033 q = 1) : d211184 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74634, d211184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74634, d211184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74635 q = 1) (hb : d208033 q = 1) : d211185 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74635, d211185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74635, d211185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56089 (p : Pattern) (ha : d74641 p = 1) (hb : d208033 p = 1) : d211191 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d208033 q = 1) : d23389 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, d23389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, d23389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56054 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d208033 q = 1) : d23390 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, d23390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, d23390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d208033 q = 1) : d23399 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d23399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56054 q ha hb
    | true =>
      simp only [d508, d23399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56057 q ha hb
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d208033 q = 1) : d23400 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d23400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, d23400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d510 q = 1) (hb : d208033 q = 1) : d23401 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d23401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d510, d23401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74620 q = 1) (hb : d208033 q = 1) : d211169 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74620, d211169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56073 q ha hb
    | true =>
      simp only [d74620, d211169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56080 q ha hb
  have h7 (q : Pattern) (ha : d645 q = 1) (hb : d208033 q = 1) : d23520 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, d23520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56058 q ha hb
    | true =>
      simp only [d645, d23520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56059 q ha hb
  have h8 (q : Pattern) (ha : d74621 q = 1) (hb : d208033 q = 1) : d211170 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74621, d211170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74621, d211170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74622 q = 1) (hb : d208033 q = 1) : d211171 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74622, d211171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74622, d211171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d74623 q = 1) (hb : d208033 q = 1) : d211172 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74623, d211172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74623, d211172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74627 q = 1) (hb : d208033 q = 1) : d211176 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74627, d211176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74627, d211176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56081 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d208033 q = 1) : d23529 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d23529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d23529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56060 q ha hb
  have h13 (q : Pattern) (ha : d74628 q = 1) (hb : d208033 q = 1) : d211177 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74628, d211177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74628, d211177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74629 q = 1) (hb : d208033 q = 1) : d211178 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74629, d211178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74629, d211178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d74630 q = 1) (hb : d208033 q = 1) : d211179 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74630, d211179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74630, d211179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d74631 q = 1) (hb : d208033 q = 1) : d211180 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74631, d211180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74631, d211180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74636 q = 1) (hb : d208033 q = 1) : d211186 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74636, d211186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74636, d211186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56088 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d208033 q = 1) : d23616 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d23616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d23616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56063 q ha hb
  have h19 (q : Pattern) (ha : d74637 q = 1) (hb : d208033 q = 1) : d211187 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74637, d211187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74637, d211187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d74638 q = 1) (hb : d208033 q = 1) : d211188 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74638, d211188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74638, d211188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d74639 q = 1) (hb : d208033 q = 1) : d211189 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74639, d211189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74639, d211189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d74640 q = 1) (hb : d208033 q = 1) : d211190 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74640, d211190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74640, d211190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d74641 q = 1) (hb : d208033 q = 1) : d211191 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74641, d211191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74641, d211191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro56090 (p : Pattern) (ha : d74647 p = 1) (hb : d208033 p = 1) : d211197 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74642 q = 1) (hb : d208033 q = 1) : d211192 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74642, d211192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74642, d211192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56089 q ha hb
  have h2 (q : Pattern) (ha : d74643 q = 1) (hb : d208033 q = 1) : d211193 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74643, d211193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74643, d211193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74644 q = 1) (hb : d208033 q = 1) : d211194 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74644, d211194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74644, d211194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74645 q = 1) (hb : d208033 q = 1) : d211195 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74645, d211195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74645, d211195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74646 q = 1) (hb : d208033 q = 1) : d211196 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74646, d211196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74646, d211196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74647 q = 1) (hb : d208033 q = 1) : d211197 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74647, d211197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74647, d211197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56091 (p : Pattern) (ha : d750 p = 1) (hb : d208033 p = 1) : d5450 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d135 q = 1) : d135 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d136 q = 1) (hb : d208033 q = 1) : d5448 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d208033, d5448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136, d208033, d5448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d137 q = 1) (hb : d208033 q = 1) : d5449 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d5449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137, d5449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d750 q = 1) (hb : d208033 q = 1) : d5450 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d750, d5450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d750, d5450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro56092 (p : Pattern) (ha : d756 p = 1) (hb : d208033 p = 1) : d23630 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d208033 q = 1) : d23422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56068 q ha hb
    | true =>
      simp only [d543, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d208033 q = 1) : d23423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d208033 q = 1) : d23424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d23424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d23424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d208033 q = 1) : d23425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d23425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d23425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d319 q = 1) (hb : d208033 q = 1) : d23231 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56031 q ha hb
    | true =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d320 q = 1) (hb : d208033 q = 1) : d23232 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d321 q = 1) (hb : d208033 q = 1) : d23233 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d23233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d23233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322 q = 1) (hb : d208033 q = 1) : d23234 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d23234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d322, d23234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d547 q = 1) (hb : d208033 q = 1) : d23426 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d547, d23426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d547, d23426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d751 q = 1) (hb : d208033 q = 1) : d5451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56091 q ha hb
    | true =>
      simp only [d751, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d752 q = 1) (hb : d208033 q = 1) : d5452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d752, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d753 q = 1) (hb : d208033 q = 1) : d5453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d5453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d5453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d754 q = 1) (hb : d208033 q = 1) : d5454 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d5454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d754, d5454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d755 q = 1) (hb : d208033 q = 1) : d23629 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d23629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d755, d23629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d756 q = 1) (hb : d208033 q = 1) : d23630 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d756, d23630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d756, d23630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56093 (p : Pattern) (ha : d758 p = 1) (hb : d208033 p = 1) : d23631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d208033 q = 1) : d23231 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56031 q ha hb
    | true =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d208033 q = 1) : d23232 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d208033 q = 1) : d23233 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d23233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d23233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d208033 q = 1) : d23234 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d23234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d23234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d208033 q = 1) : d5451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56091 q ha hb
    | true =>
      simp only [d751, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d208033 q = 1) : d5452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d208033 q = 1) : d5453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d5453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d5453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d208033 q = 1) : d5454 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d5454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d5454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d755 q = 1) (hb : d208033 q = 1) : d23629 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d23629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d755, d23629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d757 q = 1) (hb : d208033 q = 1) : d5455 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d5455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d757, d5455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d758 q = 1) (hb : d208033 q = 1) : d23631 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d758, d23631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d758, d23631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56094 (p : Pattern) (ha : d762 p = 1) (hb : d208033 p = 1) : d5457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d751 q = 1) (hb : d208033 q = 1) : d5451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56091 q ha hb
    | true =>
      simp only [d751, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d752 q = 1) (hb : d208033 q = 1) : d5452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d752, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d753 q = 1) (hb : d208033 q = 1) : d5453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d5453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d5453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d754 q = 1) (hb : d208033 q = 1) : d5454 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d5454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d754, d5454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d757 q = 1) (hb : d208033 q = 1) : d5455 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d5455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d757, d5455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d762 q = 1) (hb : d208033 q = 1) : d5457 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d762, d5457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d762, d5457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56095 (p : Pattern) (ha : d769 p = 1) (hb : d208033 p = 1) : d23641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d759 q = 1) (hb : d208033 q = 1) : d23632 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d23632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56092 q ha hb
    | true =>
      simp only [d759, d23632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56093 q ha hb
  have h2 (q : Pattern) (ha : d760 q = 1) (hb : d208033 q = 1) : d23633 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d23633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d23633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d761 q = 1) (hb : d208033 q = 1) : d23634 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d23634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d23634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d763 q = 1) (hb : d208033 q = 1) : d23635 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d23635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56093 q ha hb
    | true =>
      simp only [d763, d23635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56094 q ha hb
  have h5 (q : Pattern) (ha : d764 q = 1) (hb : d208033 q = 1) : d23636 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d23636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d23636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d765 q = 1) (hb : d208033 q = 1) : d23637 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d23637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d23637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d766 q = 1) (hb : d208033 q = 1) : d23638 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d766, d23638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d766, d23638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d767 q = 1) (hb : d208033 q = 1) : d23639 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d23639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d767, d23639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d768 q = 1) (hb : d208033 q = 1) : d23640 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d768, d23640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d768, d23640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d769 q = 1) (hb : d208033 q = 1) : d23641 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d769, d23641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d769, d23641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro56096 (p : Pattern) (ha : d773 p = 1) (hb : d208033 p = 1) : d23645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d763 q = 1) (hb : d208033 q = 1) : d23635 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d23635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56093 q ha hb
    | true =>
      simp only [d763, d23635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56094 q ha hb
  have h2 (q : Pattern) (ha : d764 q = 1) (hb : d208033 q = 1) : d23636 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d23636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d23636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d765 q = 1) (hb : d208033 q = 1) : d23637 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d23637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d23637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d767 q = 1) (hb : d208033 q = 1) : d23639 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d23639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d767, d23639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d772 q = 1) (hb : d208033 q = 1) : d23644 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, d23644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d772, d23644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d773 q = 1) (hb : d208033 q = 1) : d23645 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d773, d23645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d773, d23645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56097 (p : Pattern) (ha : d779 p = 1) (hb : d208033 p = 1) : d23651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d208033 q = 1) : d23642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56095 q ha hb
    | true =>
      simp only [d770, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d208033 q = 1) : d23643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d208033 q = 1) : d23646 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56096 q ha hb
    | true =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d208033 q = 1) : d23647 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d208033 q = 1) : d23648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d23648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d23648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d777 q = 1) (hb : d208033 q = 1) : d23649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d23649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d777, d23649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d778 q = 1) (hb : d208033 q = 1) : d23650 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d778, d23650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d778, d23650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d779 q = 1) (hb : d208033 q = 1) : d23651 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d779, d23651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d779, d23651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56098 (p : Pattern) (ha : d783 p = 1) (hb : d208033 p = 1) : d23655 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d208033 q = 1) : d23646 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56096 q ha hb
    | true =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d208033 q = 1) : d23647 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d208033 q = 1) : d23652 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d23652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d23652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d208033 q = 1) : d23653 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d23653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d23653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d208033 q = 1) : d23654 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d23654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d23654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d783 q = 1) (hb : d208033 q = 1) : d23655 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, d23655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, d23655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56099 (p : Pattern) (ha : d789 p = 1) (hb : d208033 p = 1) : d23661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d784 q = 1) (hb : d208033 q = 1) : d23656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d23656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56097 q ha hb
    | true =>
      simp only [d784, d23656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56098 q ha hb
  have h2 (q : Pattern) (ha : d785 q = 1) (hb : d208033 q = 1) : d23657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d23657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d785, d23657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d786 q = 1) (hb : d208033 q = 1) : d23658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d23658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d786, d23658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d787 q = 1) (hb : d208033 q = 1) : d23659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d23659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, d23659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d788 q = 1) (hb : d208033 q = 1) : d23660 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d23660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d23660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d789 q = 1) (hb : d208033 q = 1) : d23661 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d789, d23661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d789, d23661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56100 (p : Pattern) (ha : d792 p = 1) (hb : d208033 p = 1) : d23664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d208033 q = 1) : d23642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56095 q ha hb
    | true =>
      simp only [d770, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d208033 q = 1) : d23643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d208033 q = 1) : d23646 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56096 q ha hb
    | true =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d208033 q = 1) : d23647 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d208033 q = 1) : d23648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d23648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d23648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d777 q = 1) (hb : d208033 q = 1) : d23649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d23649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d777, d23649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d778 q = 1) (hb : d208033 q = 1) : d23650 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d778, d23650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d778, d23650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d792 q = 1) (hb : d208033 q = 1) : d23664 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d792, d23664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d792, d23664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56101 (p : Pattern) (ha : d793 p = 1) (hb : d208033 p = 1) : d23665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d208033 q = 1) : d23646 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56096 q ha hb
    | true =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d208033 q = 1) : d23647 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d208033 q = 1) : d23652 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d23652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d23652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d208033 q = 1) : d23653 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d23653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d23653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d208033 q = 1) : d23654 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d23654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d23654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d793 q = 1) (hb : d208033 q = 1) : d23665 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, d23665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d793, d23665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56102 (p : Pattern) (ha : d799 p = 1) (hb : d208033 p = 1) : d23671 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d784 q = 1) (hb : d208033 q = 1) : d23656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d23656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56097 q ha hb
    | true =>
      simp only [d784, d23656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56098 q ha hb
  have h2 (q : Pattern) (ha : d785 q = 1) (hb : d208033 q = 1) : d23657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d23657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d785, d23657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d786 q = 1) (hb : d208033 q = 1) : d23658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d23658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d786, d23658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d787 q = 1) (hb : d208033 q = 1) : d23659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d23659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, d23659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d788 q = 1) (hb : d208033 q = 1) : d23660 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d23660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d23660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d794 q = 1) (hb : d208033 q = 1) : d23666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d23666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56100 q ha hb
    | true =>
      simp only [d794, d23666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56101 q ha hb
  have h7 (q : Pattern) (ha : d795 q = 1) (hb : d208033 q = 1) : d23667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d23667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d795, d23667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d796 q = 1) (hb : d208033 q = 1) : d23668 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d23668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d796, d23668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d797 q = 1) (hb : d208033 q = 1) : d23669 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d23669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, d23669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d798 q = 1) (hb : d208033 q = 1) : d23670 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d23670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, d23670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d799 q = 1) (hb : d208033 q = 1) : d23671 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d799, d23671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d799, d23671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56103 (p : Pattern) (ha : d944 p = 1) (hb : d208033 p = 1) : d23793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d784 q = 1) (hb : d208033 q = 1) : d23656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d23656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56097 q ha hb
    | true =>
      simp only [d784, d23656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56098 q ha hb
  have h2 (q : Pattern) (ha : d785 q = 1) (hb : d208033 q = 1) : d23657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d23657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d785, d23657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d786 q = 1) (hb : d208033 q = 1) : d23658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d23658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d786, d23658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d787 q = 1) (hb : d208033 q = 1) : d23659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d23659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, d23659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d788 q = 1) (hb : d208033 q = 1) : d23660 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d23660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d23660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d208033 q = 1) : d23788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d23788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56098 q ha hb
    | true =>
      simp only [d939, d23788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d208033 q = 1) : d23789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d23789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d23789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d208033 q = 1) : d23790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d23790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d23790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d208033 q = 1) : d23791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d23791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d23791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d208033 q = 1) : d23792 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d23792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d23792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d944 q = 1) (hb : d208033 q = 1) : d23793 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d944, d23793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d944, d23793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56104 (p : Pattern) (ha : d950 p = 1) (hb : d208033 p = 1) : d23799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d208033 q = 1) : d23788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d23788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56098 q ha hb
    | true =>
      simp only [d939, d23788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d208033 q = 1) : d23789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d23789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d23789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d208033 q = 1) : d23790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d23790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, d23790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d208033 q = 1) : d23791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d23791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d23791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d208033 q = 1) : d23792 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d23792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d23792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d945 q = 1) (hb : d208033 q = 1) : d23794 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d23794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56101 q ha hb
    | true =>
      simp only [d945, d23794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d946 q = 1) (hb : d208033 q = 1) : d23795 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d23795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d23795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d947 q = 1) (hb : d208033 q = 1) : d23796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d23796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d947, d23796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d948 q = 1) (hb : d208033 q = 1) : d23797 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d23797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d23797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d949 q = 1) (hb : d208033 q = 1) : d23798 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d23798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d23798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d950 q = 1) (hb : d208033 q = 1) : d23799 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, d23799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d950, d23799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56105 (p : Pattern) (ha : d959 p = 1) (hb : d208033 p = 1) : d23808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d945 q = 1) (hb : d208033 q = 1) : d23794 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d23794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56101 q ha hb
    | true =>
      simp only [d945, d23794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d946 q = 1) (hb : d208033 q = 1) : d23795 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d23795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d23795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d208033 q = 1) : d23796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d23796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d947, d23796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d208033 q = 1) : d23797 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d23797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d23797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d208033 q = 1) : d23798 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d23798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d23798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d208033 q = 1) : d23808 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, d23808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, d23808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56106 (p : Pattern) (ha : d981 p = 1) (hb : d208033 p = 1) : d23825 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d208033 q = 1) : d23310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d23310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d23310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56031 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d208033 q = 1) : d23231 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56031 q ha hb
    | true =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d208033 q = 1) : d23311 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d23311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d23311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d208033 q = 1) : d23232 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d208033 q = 1) : d23312 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d23312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d23312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d208033 q = 1) : d23313 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d23313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d23313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d208033 q = 1) : d5495 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d5495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d5495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56091 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d208033 q = 1) : d5451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56091 q ha hb
    | true =>
      simp only [d751, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d208033 q = 1) : d5496 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d5496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d5496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d208033 q = 1) : d5452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d208033 q = 1) : d5497 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d5497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d5497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d208033 q = 1) : d5498 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d5498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d5498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d975 q = 1) (hb : d208033 q = 1) : d23820 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d23820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d975, d23820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d980 q = 1) (hb : d208033 q = 1) : d5499 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d5499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d980, d5499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d981 q = 1) (hb : d208033 q = 1) : d23825 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d981, d23825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d981, d23825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56107 (p : Pattern) (ha : d986 p = 1) (hb : d208033 p = 1) : d5501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d971 q = 1) (hb : d208033 q = 1) : d5495 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d5495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d5495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56091 q ha hb
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d208033 q = 1) : d5451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56091 q ha hb
    | true =>
      simp only [d751, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d972 q = 1) (hb : d208033 q = 1) : d5496 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d5496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d972, d5496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d752 q = 1) (hb : d208033 q = 1) : d5452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d973 q = 1) (hb : d208033 q = 1) : d5497 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d5497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d973, d5497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d974 q = 1) (hb : d208033 q = 1) : d5498 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d5498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d974, d5498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d980 q = 1) (hb : d208033 q = 1) : d5499 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d5499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d980, d5499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d986 q = 1) (hb : d208033 q = 1) : d5501 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d986, d5501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d986, d5501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56108 (p : Pattern) (ha : d1005 p = 1) (hb : d208033 p = 1) : d23848 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d987 q = 1) (hb : d208033 q = 1) : d23830 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d23830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56106 q ha hb
    | true =>
      simp only [d987, d23830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56107 q ha hb
  have h2 (q : Pattern) (ha : d988 q = 1) (hb : d208033 q = 1) : d23831 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d23831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d23831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d989 q = 1) (hb : d208033 q = 1) : d23832 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d23832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d23832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d995 q = 1) (hb : d208033 q = 1) : d23838 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d23838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d995, d23838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1004 q = 1) (hb : d208033 q = 1) : d23847 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d23847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1004, d23847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1005 q = 1) (hb : d208033 q = 1) : d23848 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, d23848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1005, d23848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56109 (p : Pattern) (ha : d1063 p = 1) (hb : d208033 p = 1) : d23906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d208033 q = 1) : d23849 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d23849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56108 q ha hb
    | true =>
      simp only [d1006, d23849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d208033 q = 1) : d23850 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d23850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d23850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1060 q = 1) (hb : d208033 q = 1) : d23903 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d23903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, d23903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d208033 q = 1) : d23904 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, d23904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1061, d23904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d208033 q = 1) : d23905 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, d23905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, d23905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d208033 q = 1) : d23906 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, d23906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, d23906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56110 (p : Pattern) (ha : d1069 p = 1) (hb : d208033 p = 1) : d23912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d208033 q = 1) : d23907 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, d23907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56109 q ha hb
    | true =>
      simp only [d1064, d23907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d208033 q = 1) : d23908 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d23908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, d23908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d208033 q = 1) : d23909 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d23909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, d23909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d208033 q = 1) : d23910 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, d23910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, d23910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d208033 q = 1) : d23911 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, d23911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, d23911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d208033 q = 1) : d23912 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, d23912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, d23912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56111 (p : Pattern) (ha : d804 p = 1) (hb : d208033 p = 1) : d23676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d208033 q = 1) : d23642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56095 q ha hb
    | true =>
      simp only [d770, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d208033 q = 1) : d23643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d208033 q = 1) : d23646 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56096 q ha hb
    | true =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d208033 q = 1) : d23647 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d208033 q = 1) : d23648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d23648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d23648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d777 q = 1) (hb : d208033 q = 1) : d23649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d23649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d777, d23649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d803 q = 1) (hb : d208033 q = 1) : d23675 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d803, d23675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d803, d23675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d804 q = 1) (hb : d208033 q = 1) : d23676 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d804, d23676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d804, d23676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56112 (p : Pattern) (ha : d806 p = 1) (hb : d208033 p = 1) : d23678 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d208033 q = 1) : d23646 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56096 q ha hb
    | true =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d208033 q = 1) : d23647 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d208033 q = 1) : d23652 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d23652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d23652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d208033 q = 1) : d23653 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d23653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d23653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d208033 q = 1) : d23677 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d23677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d23677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d806 q = 1) (hb : d208033 q = 1) : d23678 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d23678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d23678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56113 (p : Pattern) (ha : d813 p = 1) (hb : d208033 p = 1) : d23685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d208033 q = 1) : d23642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56095 q ha hb
    | true =>
      simp only [d770, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d208033 q = 1) : d23643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d208033 q = 1) : d23646 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56096 q ha hb
    | true =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d208033 q = 1) : d23647 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d208033 q = 1) : d23648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d23648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d23648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d811 q = 1) (hb : d208033 q = 1) : d23683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d811, d23683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d811, d23683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d812 q = 1) (hb : d208033 q = 1) : d23684 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d812, d23684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d812, d23684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d813 q = 1) (hb : d208033 q = 1) : d23685 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d813, d23685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d813, d23685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56114 (p : Pattern) (ha : d816 p = 1) (hb : d208033 p = 1) : d23688 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d208033 q = 1) : d23646 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56096 q ha hb
    | true =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d208033 q = 1) : d23647 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d208033 q = 1) : d23652 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d23652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d23652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d208033 q = 1) : d23686 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d23686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d23686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d208033 q = 1) : d23687 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d23687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d23687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d208033 q = 1) : d23688 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d23688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d23688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56115 (p : Pattern) (ha : d833 p = 1) (hb : d208033 p = 1) : d23694 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d824 q = 1) : d824 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d830 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d831 q = 1) (hb : d208033 q = 1) : d23692 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d831, d208033, d23692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d831, d208033, d23692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d832 q = 1) (hb : d208033 q = 1) : d23693 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d832, d23693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d832, d23693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d533 q = 1) : d533 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d539 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d540 q = 1) (hb : d208033 q = 1) : d23419 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d540, d208033, d23419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d540, d208033, d23419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d541 q = 1) (hb : d208033 q = 1) : d23420 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d541, d23420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d541, d23420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d833 q = 1) (hb : d208033 q = 1) : d23694 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d833, d23694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d833, d23694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro56116 (p : Pattern) (ha : d839 p = 1) (hb : d208033 p = 1) : d23700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d834 q = 1) (hb : d208033 q = 1) : d23695 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d23695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56115 q ha hb
    | true =>
      simp only [d834, d23695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d835 q = 1) (hb : d208033 q = 1) : d23696 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d23696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d835, d23696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d836 q = 1) (hb : d208033 q = 1) : d23697 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d836, d23697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d836, d23697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d837 q = 1) (hb : d208033 q = 1) : d23698 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d837, d23698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d837, d23698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d543 q = 1) (hb : d208033 q = 1) : d23422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56068 q ha hb
    | true =>
      simp only [d543, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d544 q = 1) (hb : d208033 q = 1) : d23423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d544, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d545 q = 1) (hb : d208033 q = 1) : d23424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d23424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d23424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d546 q = 1) (hb : d208033 q = 1) : d23425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d23425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d546, d23425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d838 q = 1) (hb : d208033 q = 1) : d23699 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d838, d23699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d838, d23699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319 q = 1) (hb : d208033 q = 1) : d23231 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56031 q ha hb
    | true =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d320 q = 1) (hb : d208033 q = 1) : d23232 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d321 q = 1) (hb : d208033 q = 1) : d23233 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d23233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d23233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d322 q = 1) (hb : d208033 q = 1) : d23234 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d23234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d322, d23234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d547 q = 1) (hb : d208033 q = 1) : d23426 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d547, d23426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d547, d23426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d839 q = 1) (hb : d208033 q = 1) : d23700 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d839, d23700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d839, d23700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56117 (p : Pattern) (ha : d845 p = 1) (hb : d208033 p = 1) : d23706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d840 q = 1) (hb : d208033 q = 1) : d23701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d840, d23701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56116 q ha hb
    | true =>
      simp only [d840, d23701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56092 q ha hb
  have h2 (q : Pattern) (ha : d841 q = 1) (hb : d208033 q = 1) : d23702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d841, d23702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d841, d23702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d842 q = 1) (hb : d208033 q = 1) : d23703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d842, d23703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d842, d23703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d759 q = 1) (hb : d208033 q = 1) : d23632 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d23632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56092 q ha hb
    | true =>
      simp only [d759, d23632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56093 q ha hb
  have h5 (q : Pattern) (ha : d760 q = 1) (hb : d208033 q = 1) : d23633 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d23633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d23633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d761 q = 1) (hb : d208033 q = 1) : d23634 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d23634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d23634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d843 q = 1) (hb : d208033 q = 1) : d23704 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d843, d23704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d843, d23704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d763 q = 1) (hb : d208033 q = 1) : d23635 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d23635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56093 q ha hb
    | true =>
      simp only [d763, d23635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56094 q ha hb
  have h9 (q : Pattern) (ha : d764 q = 1) (hb : d208033 q = 1) : d23636 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d23636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d23636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d765 q = 1) (hb : d208033 q = 1) : d23637 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d23637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d23637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d766 q = 1) (hb : d208033 q = 1) : d23638 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d766, d23638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d766, d23638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d844 q = 1) (hb : d208033 q = 1) : d23705 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d844, d23705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d844, d23705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d845 q = 1) (hb : d208033 q = 1) : d23706 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d845, d23706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d845, d23706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro56118 (p : Pattern) (ha : d851 p = 1) (hb : d208033 p = 1) : d23712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d846 q = 1) (hb : d208033 q = 1) : d23707 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d846, d23707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56117 q ha hb
    | true =>
      simp only [d846, d23707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d847 q = 1) (hb : d208033 q = 1) : d23708 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d847, d23708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d847, d23708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d770 q = 1) (hb : d208033 q = 1) : d23642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56095 q ha hb
    | true =>
      simp only [d770, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d771 q = 1) (hb : d208033 q = 1) : d23643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d848 q = 1) (hb : d208033 q = 1) : d23709 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d848, d23709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d848, d23709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d849 q = 1) (hb : d208033 q = 1) : d23710 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d849, d23710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d849, d23710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d850 q = 1) (hb : d208033 q = 1) : d23711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d850, d23711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d850, d23711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d851 q = 1) (hb : d208033 q = 1) : d23712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d851, d23712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d851, d23712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56119 (p : Pattern) (ha : d5456 p = 1) (hb : d208033 p = 1) : d23631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d208033 q = 1) : d23231 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56031 q ha hb
    | true =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d208033 q = 1) : d23232 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d208033 q = 1) : d23233 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d23233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d23233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d208033 q = 1) : d23234 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d23234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d23234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d208033 q = 1) : d5451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56091 q ha hb
    | true =>
      simp only [d751, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d208033 q = 1) : d5452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d208033 q = 1) : d5453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d5453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d5453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d208033 q = 1) : d5454 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d5454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d5454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d755 q = 1) (hb : d208033 q = 1) : d23629 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d23629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d755, d23629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5455 q = 1) (hb : d208033 q = 1) : d5455 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5456 q = 1) (hb : d208033 q = 1) : d23631 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5456, d23631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5456, d23631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56120 (p : Pattern) (ha : d5463 p = 1) (hb : d208033 p = 1) : d23641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d759 q = 1) (hb : d208033 q = 1) : d23632 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d23632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56092 q ha hb
    | true =>
      simp only [d759, d23632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56093 q ha hb
  have h2 (q : Pattern) (ha : d760 q = 1) (hb : d208033 q = 1) : d23633 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d23633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d23633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d761 q = 1) (hb : d208033 q = 1) : d23634 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d23634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d23634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d763 q = 1) (hb : d208033 q = 1) : d23635 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d23635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56093 q ha hb
    | true =>
      simp only [d763, d23635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56094 q ha hb
  have h5 (q : Pattern) (ha : d764 q = 1) (hb : d208033 q = 1) : d23636 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d23636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d23636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d765 q = 1) (hb : d208033 q = 1) : d23637 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d23637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d23637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d766 q = 1) (hb : d208033 q = 1) : d23638 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d766, d23638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d766, d23638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5457 q = 1) (hb : d208033 q = 1) : d5457 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d5458 q = 1) (hb : d208033 q = 1) : d23635 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5458, d23635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56119 q ha hb
    | true =>
      simp only [d5458, d23635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5459 q = 1) (hb : d208033 q = 1) : d23636 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5459, d23636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5459, d23636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5460 q = 1) (hb : d208033 q = 1) : d23637 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5460, d23637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5460, d23637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5461 q = 1) (hb : d208033 q = 1) : d23639 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5461, d23639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5461, d23639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5462 q = 1) (hb : d208033 q = 1) : d23640 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5462, d23640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5462, d23640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5463 q = 1) (hb : d208033 q = 1) : d23641 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5463, d23641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5463, d23641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro56121 (p : Pattern) (ha : d5469 p = 1) (hb : d208033 p = 1) : d23756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5464 q = 1) (hb : d208033 q = 1) : d23642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5464, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56120 q ha hb
    | true =>
      simp only [d5464, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5465 q = 1) (hb : d208033 q = 1) : d23643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5465, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5465, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5466 q = 1) (hb : d208033 q = 1) : d23753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5466, d23753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5466, d23753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5467 q = 1) (hb : d208033 q = 1) : d23754 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5467, d23754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5467, d23754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5468 q = 1) (hb : d208033 q = 1) : d23755 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5468, d23755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5468, d23755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5469 q = 1) (hb : d208033 q = 1) : d23756 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5469, d23756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5469, d23756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56122 (p : Pattern) (ha : d74652 p = 1) (hb : d208033 p = 1) : d211203 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d807 q = 1) (hb : d208033 q = 1) : d23679 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d23679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56111 q ha hb
    | true =>
      simp only [d807, d23679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56112 q ha hb
  have h2 (q : Pattern) (ha : d808 q = 1) (hb : d208033 q = 1) : d23680 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d23680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d808, d23680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d809 q = 1) (hb : d208033 q = 1) : d23681 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d23681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d809, d23681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d810 q = 1) (hb : d208033 q = 1) : d23682 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d23682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, d23682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d817 q = 1) (hb : d208033 q = 1) : d23689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d23689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56113 q ha hb
    | true =>
      simp only [d817, d23689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56114 q ha hb
  have h6 (q : Pattern) (ha : d818 q = 1) (hb : d208033 q = 1) : d23690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d23690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d818, d23690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d819 q = 1) (hb : d208033 q = 1) : d23691 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d23691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d819, d23691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d852 q = 1) (hb : d208033 q = 1) : d23713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d23713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56118 q ha hb
    | true =>
      simp only [d852, d23713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56097 q ha hb
  have h9 (q : Pattern) (ha : d4446 q = 1) (hb : d208033 q = 1) : d211199 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d211199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4446, d211199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5470 q = 1) (hb : d208033 q = 1) : d23757 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5470, d23757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56121 q ha hb
    | true =>
      simp only [d5470, d23757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5471 q = 1) (hb : d208033 q = 1) : d23758 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5471, d23758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5471, d23758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74649 q = 1) (hb : d208033 q = 1) : d211200 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74649, d211200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74649, d211200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74650 q = 1) (hb : d208033 q = 1) : d211201 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74650, d211201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74650, d211201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74651 q = 1) (hb : d208033 q = 1) : d211202 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74651, d211202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74651, d211202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74652 q = 1) (hb : d208033 q = 1) : d211203 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74652, d211203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74652, d211203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56123 (p : Pattern) (ha : d915 p = 1) (hb : d208033 p = 1) : d23763 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d208033 q = 1) : d23642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56095 q ha hb
    | true =>
      simp only [d770, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d208033 q = 1) : d23643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d208033 q = 1) : d23646 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56096 q ha hb
    | true =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d208033 q = 1) : d23647 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d208033 q = 1) : d23648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d23648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d23648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d777 q = 1) (hb : d208033 q = 1) : d23649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d23649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d777, d23649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d803 q = 1) (hb : d208033 q = 1) : d23675 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d803, d23675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d803, d23675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d915 q = 1) (hb : d208033 q = 1) : d23763 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d915, d23763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d915, d23763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56124 (p : Pattern) (ha : d916 p = 1) (hb : d208033 p = 1) : d23764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d208033 q = 1) : d23646 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56096 q ha hb
    | true =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d208033 q = 1) : d23647 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d208033 q = 1) : d23652 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d23652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d23652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d208033 q = 1) : d23653 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d23653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d23653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d208033 q = 1) : d23677 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d23677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d23677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d916 q = 1) (hb : d208033 q = 1) : d23764 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, d23764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d916, d23764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56125 (p : Pattern) (ha : d921 p = 1) (hb : d208033 p = 1) : d23769 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d208033 q = 1) : d23642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56095 q ha hb
    | true =>
      simp only [d770, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d208033 q = 1) : d23643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d208033 q = 1) : d23646 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56096 q ha hb
    | true =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d208033 q = 1) : d23647 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d208033 q = 1) : d23648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d23648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d23648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d811 q = 1) (hb : d208033 q = 1) : d23683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d811, d23683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d811, d23683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d812 q = 1) (hb : d208033 q = 1) : d23684 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d812, d23684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d812, d23684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d921 q = 1) (hb : d208033 q = 1) : d23769 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d921, d23769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d921, d23769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56126 (p : Pattern) (ha : d922 p = 1) (hb : d208033 p = 1) : d23770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d208033 q = 1) : d23646 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56096 q ha hb
    | true =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d208033 q = 1) : d23647 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d208033 q = 1) : d23652 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d23652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d23652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d208033 q = 1) : d23686 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d23686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d23686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d208033 q = 1) : d23687 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d23687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d23687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d922 q = 1) (hb : d208033 q = 1) : d23770 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, d23770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d922, d23770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56127 (p : Pattern) (ha : d926 p = 1) (hb : d208033 p = 1) : d23774 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d846 q = 1) (hb : d208033 q = 1) : d23707 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d846, d23707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56117 q ha hb
    | true =>
      simp only [d846, d23707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d847 q = 1) (hb : d208033 q = 1) : d23708 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d847, d23708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d847, d23708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d770 q = 1) (hb : d208033 q = 1) : d23642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56095 q ha hb
    | true =>
      simp only [d770, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d771 q = 1) (hb : d208033 q = 1) : d23643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d848 q = 1) (hb : d208033 q = 1) : d23709 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d848, d23709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d848, d23709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d849 q = 1) (hb : d208033 q = 1) : d23710 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d849, d23710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d849, d23710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d850 q = 1) (hb : d208033 q = 1) : d23711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d850, d23711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d850, d23711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d926 q = 1) (hb : d208033 q = 1) : d23774 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d926, d23774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d926, d23774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56128 (p : Pattern) (ha : d5476 p = 1) (hb : d208033 p = 1) : d23780 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5464 q = 1) (hb : d208033 q = 1) : d23642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5464, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56120 q ha hb
    | true =>
      simp only [d5464, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5465 q = 1) (hb : d208033 q = 1) : d23643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5465, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5465, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5466 q = 1) (hb : d208033 q = 1) : d23753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5466, d23753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5466, d23753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5467 q = 1) (hb : d208033 q = 1) : d23754 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5467, d23754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5467, d23754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5468 q = 1) (hb : d208033 q = 1) : d23755 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5468, d23755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5468, d23755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5476 q = 1) (hb : d208033 q = 1) : d23780 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5476, d23780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5476, d23780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56129 (p : Pattern) (ha : d74656 p = 1) (hb : d208033 p = 1) : d211208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d807 q = 1) (hb : d208033 q = 1) : d23679 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d23679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56111 q ha hb
    | true =>
      simp only [d807, d23679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56112 q ha hb
  have h2 (q : Pattern) (ha : d808 q = 1) (hb : d208033 q = 1) : d23680 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d23680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d808, d23680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d809 q = 1) (hb : d208033 q = 1) : d23681 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d23681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d809, d23681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d810 q = 1) (hb : d208033 q = 1) : d23682 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d23682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, d23682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d817 q = 1) (hb : d208033 q = 1) : d23689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d23689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56113 q ha hb
    | true =>
      simp only [d817, d23689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56114 q ha hb
  have h6 (q : Pattern) (ha : d818 q = 1) (hb : d208033 q = 1) : d23690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d23690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d818, d23690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d819 q = 1) (hb : d208033 q = 1) : d23691 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d23691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d819, d23691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d852 q = 1) (hb : d208033 q = 1) : d23713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d23713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56118 q ha hb
    | true =>
      simp only [d852, d23713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56097 q ha hb
  have h9 (q : Pattern) (ha : d4446 q = 1) (hb : d208033 q = 1) : d211199 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d211199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4446, d211199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5470 q = 1) (hb : d208033 q = 1) : d23757 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5470, d23757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56121 q ha hb
    | true =>
      simp only [d5470, d23757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5471 q = 1) (hb : d208033 q = 1) : d23758 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5471, d23758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5471, d23758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74649 q = 1) (hb : d208033 q = 1) : d211200 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74649, d211200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74649, d211200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74650 q = 1) (hb : d208033 q = 1) : d211201 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74650, d211201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74650, d211201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74651 q = 1) (hb : d208033 q = 1) : d211202 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74651, d211202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74651, d211202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d917 q = 1) (hb : d208033 q = 1) : d23765 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d917, d23765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56123 q ha hb
    | true =>
      simp only [d917, d23765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56124 q ha hb
  have h16 (q : Pattern) (ha : d918 q = 1) (hb : d208033 q = 1) : d23766 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d918, d23766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d918, d23766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d919 q = 1) (hb : d208033 q = 1) : d23767 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d919, d23767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d919, d23767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d920 q = 1) (hb : d208033 q = 1) : d23768 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d920, d23768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d920, d23768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d923 q = 1) (hb : d208033 q = 1) : d23771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d923, d23771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56125 q ha hb
    | true =>
      simp only [d923, d23771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56126 q ha hb
  have h20 (q : Pattern) (ha : d924 q = 1) (hb : d208033 q = 1) : d23772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d924, d23772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d924, d23772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d925 q = 1) (hb : d208033 q = 1) : d23773 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d925, d23773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d925, d23773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d927 q = 1) (hb : d208033 q = 1) : d23775 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d23775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56127 q ha hb
    | true =>
      simp only [d927, d23775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56100 q ha hb
  have h23 (q : Pattern) (ha : d4451 q = 1) (hb : d208033 q = 1) : d211204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d211204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4451, d211204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d5477 q = 1) (hb : d208033 q = 1) : d23781 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5477, d23781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56128 q ha hb
    | true =>
      simp only [d5477, d23781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d5478 q = 1) (hb : d208033 q = 1) : d23782 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5478, d23782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5478, d23782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d74653 q = 1) (hb : d208033 q = 1) : d211205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74653, d211205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d74653, d211205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d74654 q = 1) (hb : d208033 q = 1) : d211206 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74654, d211206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74654, d211206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d74655 q = 1) (hb : d208033 q = 1) : d211207 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74655, d211207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74655, d211207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d74656 q = 1) (hb : d208033 q = 1) : d211208 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74656, d211208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74656, d211208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro56130 (p : Pattern) (ha : d74663 p = 1) (hb : d208033 p = 1) : d211215 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d927 q = 1) (hb : d208033 q = 1) : d23775 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d23775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56127 q ha hb
    | true =>
      simp only [d927, d23775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56100 q ha hb
  have h2 (q : Pattern) (ha : d4451 q = 1) (hb : d208033 q = 1) : d211204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d211204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4451, d211204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5477 q = 1) (hb : d208033 q = 1) : d23781 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5477, d23781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56128 q ha hb
    | true =>
      simp only [d5477, d23781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5478 q = 1) (hb : d208033 q = 1) : d23782 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5478, d23782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5478, d23782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74653 q = 1) (hb : d208033 q = 1) : d211205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74653, d211205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74653, d211205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74661 q = 1) (hb : d208033 q = 1) : d211213 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74661, d211213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74661, d211213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74662 q = 1) (hb : d208033 q = 1) : d211214 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74662, d211214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74662, d211214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74663 q = 1) (hb : d208033 q = 1) : d211215 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74663, d211215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74663, d211215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56131 (p : Pattern) (ha : d970 p = 1) (hb : d208033 p = 1) : d23819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d965 q = 1) (hb : d208033 q = 1) : d23814 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d965, d23814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d965, d23814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56115 q ha hb
  have h2 (q : Pattern) (ha : d834 q = 1) (hb : d208033 q = 1) : d23695 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d23695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56115 q ha hb
    | true =>
      simp only [d834, d23695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d966 q = 1) (hb : d208033 q = 1) : d23815 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d966, d23815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d966, d23815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d835 q = 1) (hb : d208033 q = 1) : d23696 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d23696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d835, d23696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d967 q = 1) (hb : d208033 q = 1) : d23816 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d967, d23816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d967, d23816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d968 q = 1) (hb : d208033 q = 1) : d23817 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d968, d23817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d968, d23817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d659 q = 1) (hb : d208033 q = 1) : d23534 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d23534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d23534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56068 q ha hb
  have h8 (q : Pattern) (ha : d543 q = 1) (hb : d208033 q = 1) : d23422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56068 q ha hb
    | true =>
      simp only [d543, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d660 q = 1) (hb : d208033 q = 1) : d23535 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d23535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d660, d23535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d544 q = 1) (hb : d208033 q = 1) : d23423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d544, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d661 q = 1) (hb : d208033 q = 1) : d23536 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d23536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d661, d23536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d662 q = 1) (hb : d208033 q = 1) : d23537 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d23537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d662, d23537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d969 q = 1) (hb : d208033 q = 1) : d23818 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d969, d23818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d969, d23818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d412 q = 1) (hb : d208033 q = 1) : d23310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d23310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d23310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56031 q ha hb
  have h15 (q : Pattern) (ha : d319 q = 1) (hb : d208033 q = 1) : d23231 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56031 q ha hb
    | true =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d413 q = 1) (hb : d208033 q = 1) : d23311 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d23311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d413, d23311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d320 q = 1) (hb : d208033 q = 1) : d23232 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d414 q = 1) (hb : d208033 q = 1) : d23312 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d23312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d414, d23312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d415 q = 1) (hb : d208033 q = 1) : d23313 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d23313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d415, d23313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d663 q = 1) (hb : d208033 q = 1) : d23538 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d663, d23538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d663, d23538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d970 q = 1) (hb : d208033 q = 1) : d23819 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d970, d23819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d970, d23819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro56132 (p : Pattern) (ha : d976 p = 1) (hb : d208033 p = 1) : d23821 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d208033 q = 1) : d23534 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d23534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d23534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56068 q ha hb
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d208033 q = 1) : d23422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56068 q ha hb
    | true =>
      simp only [d543, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d660 q = 1) (hb : d208033 q = 1) : d23535 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d23535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d660, d23535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d544 q = 1) (hb : d208033 q = 1) : d23423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d661 q = 1) (hb : d208033 q = 1) : d23536 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d23536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d661, d23536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d662 q = 1) (hb : d208033 q = 1) : d23537 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d23537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d662, d23537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d412 q = 1) (hb : d208033 q = 1) : d23310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d23310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d23310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56031 q ha hb
  have h8 (q : Pattern) (ha : d319 q = 1) (hb : d208033 q = 1) : d23231 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56031 q ha hb
    | true =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d413 q = 1) (hb : d208033 q = 1) : d23311 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d23311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d413, d23311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320 q = 1) (hb : d208033 q = 1) : d23232 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d414 q = 1) (hb : d208033 q = 1) : d23312 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d23312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d414, d23312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d415 q = 1) (hb : d208033 q = 1) : d23313 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d23313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d415, d23313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d663 q = 1) (hb : d208033 q = 1) : d23538 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d663, d23538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d663, d23538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d971 q = 1) (hb : d208033 q = 1) : d5495 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d5495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d5495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56091 q ha hb
  have h15 (q : Pattern) (ha : d751 q = 1) (hb : d208033 q = 1) : d5451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56091 q ha hb
    | true =>
      simp only [d751, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d972 q = 1) (hb : d208033 q = 1) : d5496 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d5496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d972, d5496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d752 q = 1) (hb : d208033 q = 1) : d5452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d752, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d973 q = 1) (hb : d208033 q = 1) : d5497 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d5497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d973, d5497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d974 q = 1) (hb : d208033 q = 1) : d5498 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d5498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d974, d5498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d975 q = 1) (hb : d208033 q = 1) : d23820 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d23820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d975, d23820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d976 q = 1) (hb : d208033 q = 1) : d23821 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d976, d23821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d976, d23821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro56133 (p : Pattern) (ha : d992 p = 1) (hb : d208033 p = 1) : d23835 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d977 q = 1) (hb : d208033 q = 1) : d23822 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d977, d23822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56131 q ha hb
    | true =>
      simp only [d977, d23822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56132 q ha hb
  have h2 (q : Pattern) (ha : d978 q = 1) (hb : d208033 q = 1) : d23823 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d978, d23823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d978, d23823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d979 q = 1) (hb : d208033 q = 1) : d23824 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d979, d23824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d979, d23824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d982 q = 1) (hb : d208033 q = 1) : d23826 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d23826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56132 q ha hb
    | true =>
      simp only [d982, d23826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56106 q ha hb
  have h5 (q : Pattern) (ha : d983 q = 1) (hb : d208033 q = 1) : d23827 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d23827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d23827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d984 q = 1) (hb : d208033 q = 1) : d23828 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d23828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d23828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d985 q = 1) (hb : d208033 q = 1) : d23829 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d985, d23829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d985, d23829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d987 q = 1) (hb : d208033 q = 1) : d23830 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d23830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56106 q ha hb
    | true =>
      simp only [d987, d23830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56107 q ha hb
  have h9 (q : Pattern) (ha : d988 q = 1) (hb : d208033 q = 1) : d23831 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d23831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d23831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d989 q = 1) (hb : d208033 q = 1) : d23832 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d23832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d23832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d990 q = 1) (hb : d208033 q = 1) : d23833 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d23833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d990, d23833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d991 q = 1) (hb : d208033 q = 1) : d23834 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d991, d23834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d991, d23834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d992 q = 1) (hb : d208033 q = 1) : d23835 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d992, d23835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d992, d23835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro56134 (p : Pattern) (ha : d997 p = 1) (hb : d208033 p = 1) : d23840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d982 q = 1) (hb : d208033 q = 1) : d23826 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d23826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56132 q ha hb
    | true =>
      simp only [d982, d23826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56106 q ha hb
  have h2 (q : Pattern) (ha : d983 q = 1) (hb : d208033 q = 1) : d23827 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d23827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d23827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d984 q = 1) (hb : d208033 q = 1) : d23828 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d23828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d23828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d987 q = 1) (hb : d208033 q = 1) : d23830 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d23830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56106 q ha hb
    | true =>
      simp only [d987, d23830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56107 q ha hb
  have h5 (q : Pattern) (ha : d988 q = 1) (hb : d208033 q = 1) : d23831 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d23831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d23831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d989 q = 1) (hb : d208033 q = 1) : d23832 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d23832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d23832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d990 q = 1) (hb : d208033 q = 1) : d23833 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d23833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d990, d23833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d995 q = 1) (hb : d208033 q = 1) : d23838 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d23838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d995, d23838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d996 q = 1) (hb : d208033 q = 1) : d23839 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d996, d23839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d996, d23839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d997 q = 1) (hb : d208033 q = 1) : d23840 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d997, d23840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d997, d23840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro56135 (p : Pattern) (ha : d1003 p = 1) (hb : d208033 p = 1) : d23846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d993 q = 1) (hb : d208033 q = 1) : d23836 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d993, d23836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56133 q ha hb
    | true =>
      simp only [d993, d23836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d994 q = 1) (hb : d208033 q = 1) : d23837 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d994, d23837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d994, d23837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d998 q = 1) (hb : d208033 q = 1) : d23841 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d998, d23841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56134 q ha hb
    | true =>
      simp only [d998, d23841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d999 q = 1) (hb : d208033 q = 1) : d23842 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d999, d23842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d999, d23842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1000 q = 1) (hb : d208033 q = 1) : d23843 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1000, d23843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1000, d23843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1001 q = 1) (hb : d208033 q = 1) : d23844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1001, d23844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1001, d23844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1002 q = 1) (hb : d208033 q = 1) : d23845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1002, d23845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1002, d23845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1003 q = 1) (hb : d208033 q = 1) : d23846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1003, d23846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1003, d23846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56136 (p : Pattern) (ha : d1011 p = 1) (hb : d208033 p = 1) : d23854 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d998 q = 1) (hb : d208033 q = 1) : d23841 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d998, d23841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56134 q ha hb
    | true =>
      simp only [d998, d23841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d999 q = 1) (hb : d208033 q = 1) : d23842 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d999, d23842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d999, d23842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d208033 q = 1) : d23849 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d23849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56108 q ha hb
    | true =>
      simp only [d1006, d23849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d208033 q = 1) : d23850 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d23850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d23850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1008 q = 1) (hb : d208033 q = 1) : d23851 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1008, d23851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1008, d23851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1009 q = 1) (hb : d208033 q = 1) : d23852 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1009, d23852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1009, d23852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1010 q = 1) (hb : d208033 q = 1) : d23853 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1010, d23853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1010, d23853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1011 q = 1) (hb : d208033 q = 1) : d23854 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1011, d23854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1011, d23854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56137 (p : Pattern) (ha : d5500 p = 1) (hb : d208033 p = 1) : d23825 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d208033 q = 1) : d23310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d23310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d23310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56031 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d208033 q = 1) : d23231 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56031 q ha hb
    | true =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d208033 q = 1) : d23311 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d23311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d23311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d208033 q = 1) : d23232 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d208033 q = 1) : d23312 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d23312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d23312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d208033 q = 1) : d23313 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d23313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d23313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d208033 q = 1) : d5495 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d5495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d5495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56091 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d208033 q = 1) : d5451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56091 q ha hb
    | true =>
      simp only [d751, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d208033 q = 1) : d5496 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d5496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d5496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d208033 q = 1) : d5452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d208033 q = 1) : d5497 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d5497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d5497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d208033 q = 1) : d5498 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d5498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d5498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d975 q = 1) (hb : d208033 q = 1) : d23820 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d23820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d975, d23820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5499 q = 1) (hb : d208033 q = 1) : d5499 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d5500 q = 1) (hb : d208033 q = 1) : d23825 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5500, d23825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5500, d23825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56138 (p : Pattern) (ha : d5507 p = 1) (hb : d208033 p = 1) : d23840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d982 q = 1) (hb : d208033 q = 1) : d23826 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d23826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56132 q ha hb
    | true =>
      simp only [d982, d23826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56106 q ha hb
  have h2 (q : Pattern) (ha : d983 q = 1) (hb : d208033 q = 1) : d23827 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d23827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d23827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d984 q = 1) (hb : d208033 q = 1) : d23828 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d23828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d23828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d987 q = 1) (hb : d208033 q = 1) : d23830 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d23830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56106 q ha hb
    | true =>
      simp only [d987, d23830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56107 q ha hb
  have h5 (q : Pattern) (ha : d988 q = 1) (hb : d208033 q = 1) : d23831 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d23831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d23831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d989 q = 1) (hb : d208033 q = 1) : d23832 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d23832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d23832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d990 q = 1) (hb : d208033 q = 1) : d23833 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d23833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d990, d23833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5501 q = 1) (hb : d208033 q = 1) : d5501 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d5502 q = 1) (hb : d208033 q = 1) : d23830 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5502, d23830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56137 q ha hb
    | true =>
      simp only [d5502, d23830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5503 q = 1) (hb : d208033 q = 1) : d23831 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5503, d23831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5503, d23831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5504 q = 1) (hb : d208033 q = 1) : d23832 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5504, d23832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5504, d23832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5505 q = 1) (hb : d208033 q = 1) : d23838 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5505, d23838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5505, d23838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5506 q = 1) (hb : d208033 q = 1) : d23839 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5506, d23839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5506, d23839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5507 q = 1) (hb : d208033 q = 1) : d23840 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5507, d23840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5507, d23840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro56139 (p : Pattern) (ha : d5513 p = 1) (hb : d208033 p = 1) : d23895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5508 q = 1) (hb : d208033 q = 1) : d23841 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5508, d23841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56138 q ha hb
    | true =>
      simp only [d5508, d23841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5509 q = 1) (hb : d208033 q = 1) : d23842 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5509, d23842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5509, d23842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5510 q = 1) (hb : d208033 q = 1) : d23892 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5510, d23892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5510, d23892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5511 q = 1) (hb : d208033 q = 1) : d23893 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5511, d23893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5511, d23893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5512 q = 1) (hb : d208033 q = 1) : d23894 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5512, d23894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5512, d23894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5513 q = 1) (hb : d208033 q = 1) : d23895 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5513, d23895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5513, d23895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56140 (p : Pattern) (ha : d74672 p = 1) (hb : d208033 p = 1) : d211225 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1012 q = 1) (hb : d208033 q = 1) : d23855 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1012, d23855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56135 q ha hb
    | true =>
      simp only [d1012, d23855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56136 q ha hb
  have h2 (q : Pattern) (ha : d4466 q = 1) (hb : d208033 q = 1) : d211221 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4466, d211221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4466, d211221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5514 q = 1) (hb : d208033 q = 1) : d23896 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5514, d23896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56139 q ha hb
    | true =>
      simp only [d5514, d23896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5515 q = 1) (hb : d208033 q = 1) : d23897 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5515, d23897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5515, d23897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74669 q = 1) (hb : d208033 q = 1) : d211222 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74669, d211222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74669, d211222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74670 q = 1) (hb : d208033 q = 1) : d211223 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74670, d211223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74670, d211223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74671 q = 1) (hb : d208033 q = 1) : d211224 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74671, d211224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74671, d211224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74672 q = 1) (hb : d208033 q = 1) : d211225 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74672, d211225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74672, d211225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56141 (p : Pattern) (ha : d74678 p = 1) (hb : d208033 p = 1) : d211231 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d208033 q = 1) : d23662 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d23662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, d23662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56099 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d208033 q = 1) : d23663 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d23663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, d23663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d208033 q = 1) : d23672 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d23672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56099 q ha hb
    | true =>
      simp only [d800, d23672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56102 q ha hb
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d208033 q = 1) : d23673 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d23673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, d23673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d802 q = 1) (hb : d208033 q = 1) : d23674 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d23674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, d23674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74657 q = 1) (hb : d208033 q = 1) : d211209 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74657, d211209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56122 q ha hb
    | true =>
      simp only [d74657, d211209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56129 q ha hb
  have h7 (q : Pattern) (ha : d951 q = 1) (hb : d208033 q = 1) : d23800 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, d23800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56103 q ha hb
    | true =>
      simp only [d951, d23800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56104 q ha hb
  have h8 (q : Pattern) (ha : d74658 q = 1) (hb : d208033 q = 1) : d211210 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74658, d211210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74658, d211210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74659 q = 1) (hb : d208033 q = 1) : d211211 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74659, d211211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74659, d211211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d74660 q = 1) (hb : d208033 q = 1) : d211212 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74660, d211212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74660, d211212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74664 q = 1) (hb : d208033 q = 1) : d211216 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74664, d211216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74664, d211216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56130 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d208033 q = 1) : d23809 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d23809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d23809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56105 q ha hb
  have h13 (q : Pattern) (ha : d74665 q = 1) (hb : d208033 q = 1) : d211217 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74665, d211217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74665, d211217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74666 q = 1) (hb : d208033 q = 1) : d211218 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74666, d211218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74666, d211218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d74667 q = 1) (hb : d208033 q = 1) : d211219 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74667, d211219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74667, d211219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d74668 q = 1) (hb : d208033 q = 1) : d211220 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74668, d211220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74668, d211220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74673 q = 1) (hb : d208033 q = 1) : d211226 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74673, d211226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74673, d211226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56140 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d208033 q = 1) : d23913 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d23913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d23913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56110 q ha hb
  have h19 (q : Pattern) (ha : d74674 q = 1) (hb : d208033 q = 1) : d211227 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74674, d211227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74674, d211227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d74675 q = 1) (hb : d208033 q = 1) : d211228 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74675, d211228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74675, d211228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d74676 q = 1) (hb : d208033 q = 1) : d211229 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74676, d211229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74676, d211229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d74677 q = 1) (hb : d208033 q = 1) : d211230 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74677, d211230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74677, d211230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d74678 q = 1) (hb : d208033 q = 1) : d211231 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74678, d211231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74678, d211231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro56142 (p : Pattern) (ha : d74684 p = 1) (hb : d208033 p = 1) : d211237 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74679 q = 1) (hb : d208033 q = 1) : d211232 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74679, d211232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74679, d211232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56141 q ha hb
  have h2 (q : Pattern) (ha : d74680 q = 1) (hb : d208033 q = 1) : d211233 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74680, d211233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74680, d211233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74681 q = 1) (hb : d208033 q = 1) : d211234 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74681, d211234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74681, d211234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74682 q = 1) (hb : d208033 q = 1) : d211235 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74682, d211235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74682, d211235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74683 q = 1) (hb : d208033 q = 1) : d211236 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74683, d211236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74683, d211236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74684 q = 1) (hb : d208033 q = 1) : d211237 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74684, d211237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74684, d211237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56143 (p : Pattern) (ha : d1099 p = 1) (hb : d208033 p = 1) : d23931 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1090 q = 1) : d1090 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d830 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1091 q = 1) (hb : d208033 q = 1) : d23927 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1091, d208033, d23927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1091, d208033, d23927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1092 q = 1) (hb : d208033 q = 1) : d23928 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1092, d23928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1092, d23928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d1096 q = 1) : d1096 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d539 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1097 q = 1) (hb : d208033 q = 1) : d23929 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1097, d208033, d23929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1097, d208033, d23929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1098 q = 1) (hb : d208033 q = 1) : d23930 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1098, d23930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1098, d23930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d1099 q = 1) (hb : d208033 q = 1) : d23931 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1099, d23931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1099, d23931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro56144 (p : Pattern) (ha : d1109 p = 1) (hb : d208033 p = 1) : d23938 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1096 q = 1) : d1096 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d539 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1097 q = 1) (hb : d208033 q = 1) : d23929 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1097, d208033, d23929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1097, d208033, d23929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1098 q = 1) (hb : d208033 q = 1) : d23930 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1098, d23930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1098, d23930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d1106 q = 1) : d1106 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d135 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1107 q = 1) (hb : d208033 q = 1) : d23936 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1107, d208033, d23936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1107, d208033, d23936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1108 q = 1) (hb : d208033 q = 1) : d23937 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1108, d23937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1108, d23937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d1109 q = 1) (hb : d208033 q = 1) : d23938 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1109, d23938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1109, d23938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro56145 (p : Pattern) (ha : d1120 p = 1) (hb : d208033 p = 1) : d23944 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1106 q = 1) : d1106 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1107 q = 1) (hb : d208033 q = 1) : d23936 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1107, d208033, d23936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1107, d208033, d23936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1108 q = 1) (hb : d208033 q = 1) : d23937 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1108, d23937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1108, d23937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d1117 q = 1) : d1117 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1118 q = 1) (hb : d208033 q = 1) : d5537 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1118, d208033, d5537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1118, d208033, d5537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1119 q = 1) (hb : d208033 q = 1) : d5538 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1119, d5538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1119, d5538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d1120 q = 1) (hb : d208033 q = 1) : d23944 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1120, d23944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1120, d23944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro56146 (p : Pattern) (ha : d1126 p = 1) (hb : d208033 p = 1) : d23950 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1100 q = 1) (hb : d208033 q = 1) : d23932 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d23932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56143 q ha hb
    | true =>
      simp only [d1100, d23932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1101 q = 1) (hb : d208033 q = 1) : d23933 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d23933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1101, d23933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1102 q = 1) (hb : d208033 q = 1) : d23934 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d23934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1102, d23934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1103 q = 1) (hb : d208033 q = 1) : d23935 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d23935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1103, d23935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1110 q = 1) (hb : d208033 q = 1) : d23939 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d23939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56144 q ha hb
    | true =>
      simp only [d1110, d23939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1111 q = 1) (hb : d208033 q = 1) : d23940 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d23940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1111, d23940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1112 q = 1) (hb : d208033 q = 1) : d23941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d23941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d23941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1113 q = 1) (hb : d208033 q = 1) : d23942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d23942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1113, d23942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1114 q = 1) (hb : d208033 q = 1) : d23943 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1114, d23943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1114, d23943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1121 q = 1) (hb : d208033 q = 1) : d23945 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d23945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56145 q ha hb
    | true =>
      simp only [d1121, d23945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1122 q = 1) (hb : d208033 q = 1) : d23946 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d23946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1122, d23946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1123 q = 1) (hb : d208033 q = 1) : d23947 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d23947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d23947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1124 q = 1) (hb : d208033 q = 1) : d23948 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d23948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1124, d23948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d1125 q = 1) (hb : d208033 q = 1) : d23949 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d23949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1125, d23949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1126 q = 1) (hb : d208033 q = 1) : d23950 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1126, d23950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1126, d23950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56147 (p : Pattern) (ha : d1128 p = 1) (hb : d208033 p = 1) : d23952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1110 q = 1) (hb : d208033 q = 1) : d23939 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d23939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56144 q ha hb
    | true =>
      simp only [d1110, d23939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1111 q = 1) (hb : d208033 q = 1) : d23940 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d23940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1111, d23940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1112 q = 1) (hb : d208033 q = 1) : d23941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d23941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d23941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1113 q = 1) (hb : d208033 q = 1) : d23942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d23942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1113, d23942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1121 q = 1) (hb : d208033 q = 1) : d23945 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d23945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56145 q ha hb
    | true =>
      simp only [d1121, d23945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1122 q = 1) (hb : d208033 q = 1) : d23946 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d23946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1122, d23946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1123 q = 1) (hb : d208033 q = 1) : d23947 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d23947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d23947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1124 q = 1) (hb : d208033 q = 1) : d23948 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d23948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1124, d23948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1125 q = 1) (hb : d208033 q = 1) : d23949 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d23949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1125, d23949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1127 q = 1) (hb : d208033 q = 1) : d23951 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, d23951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1127, d23951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1128 q = 1) (hb : d208033 q = 1) : d23952 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1128, d23952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1128, d23952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56148 (p : Pattern) (ha : d1141 p = 1) (hb : d208033 p = 1) : d23956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1121 q = 1) (hb : d208033 q = 1) : d23945 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d23945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56145 q ha hb
    | true =>
      simp only [d1121, d23945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1122 q = 1) (hb : d208033 q = 1) : d23946 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d23946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1122, d23946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1123 q = 1) (hb : d208033 q = 1) : d23947 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d23947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d23947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1124 q = 1) (hb : d208033 q = 1) : d23948 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d23948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1124, d23948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1127 q = 1) (hb : d208033 q = 1) : d23951 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, d23951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1127, d23951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1140 q = 1) (hb : d208033 q = 1) : d1140 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1141 q = 1) (hb : d208033 q = 1) : d23956 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1141, d23956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1141, d23956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro56149 (p : Pattern) (ha : d1148 p = 1) (hb : d208033 p = 1) : d23963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1129 q = 1) (hb : d208033 q = 1) : d23953 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d23953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56146 q ha hb
    | true =>
      simp only [d1129, d23953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56147 q ha hb
  have h2 (q : Pattern) (ha : d1130 q = 1) (hb : d208033 q = 1) : d23954 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d23954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d23954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1131 q = 1) (hb : d208033 q = 1) : d23955 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d23955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d23955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1142 q = 1) (hb : d208033 q = 1) : d23957 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d23957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56147 q ha hb
    | true =>
      simp only [d1142, d23957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56148 q ha hb
  have h5 (q : Pattern) (ha : d1143 q = 1) (hb : d208033 q = 1) : d23958 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d23958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d23958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1144 q = 1) (hb : d208033 q = 1) : d23959 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d23959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d23959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1145 q = 1) (hb : d208033 q = 1) : d23960 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, d23960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1145, d23960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1146 q = 1) (hb : d208033 q = 1) : d23961 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1146, d23961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1146, d23961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1147 q = 1) (hb : d208033 q = 1) : d23962 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1147, d23962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1147, d23962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1148 q = 1) (hb : d208033 q = 1) : d23963 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1148, d23963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1148, d23963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro56150 (p : Pattern) (ha : d1152 p = 1) (hb : d208033 p = 1) : d23967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1142 q = 1) (hb : d208033 q = 1) : d23957 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d23957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56147 q ha hb
    | true =>
      simp only [d1142, d23957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56148 q ha hb
  have h2 (q : Pattern) (ha : d1143 q = 1) (hb : d208033 q = 1) : d23958 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d23958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d23958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1144 q = 1) (hb : d208033 q = 1) : d23959 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d23959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d23959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1146 q = 1) (hb : d208033 q = 1) : d23961 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1146, d23961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1146, d23961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1151 q = 1) (hb : d208033 q = 1) : d23966 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1151, d23966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1151, d23966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1152 q = 1) (hb : d208033 q = 1) : d23967 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1152, d23967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1152, d23967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56151 (p : Pattern) (ha : d1158 p = 1) (hb : d208033 p = 1) : d23973 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d208033 q = 1) : d23964 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d23964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56149 q ha hb
    | true =>
      simp only [d1149, d23964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d208033 q = 1) : d23965 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d23965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d23965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d208033 q = 1) : d23968 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56150 q ha hb
    | true =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d208033 q = 1) : d23969 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d208033 q = 1) : d23970 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d23970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d23970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d208033 q = 1) : d23971 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d23971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1156, d23971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1157 q = 1) (hb : d208033 q = 1) : d23972 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1157, d23972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1157, d23972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1158 q = 1) (hb : d208033 q = 1) : d23973 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1158, d23973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1158, d23973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56152 (p : Pattern) (ha : d1162 p = 1) (hb : d208033 p = 1) : d23977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d208033 q = 1) : d23968 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56150 q ha hb
    | true =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d208033 q = 1) : d23969 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d208033 q = 1) : d23974 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d23974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d23974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d208033 q = 1) : d23975 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d23975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d23975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1161 q = 1) (hb : d208033 q = 1) : d23976 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, d23976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1161, d23976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1162 q = 1) (hb : d208033 q = 1) : d23977 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1162, d23977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1162, d23977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56153 (p : Pattern) (ha : d1168 p = 1) (hb : d208033 p = 1) : d23983 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1163 q = 1) (hb : d208033 q = 1) : d23978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d23978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56151 q ha hb
    | true =>
      simp only [d1163, d23978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56152 q ha hb
  have h2 (q : Pattern) (ha : d1164 q = 1) (hb : d208033 q = 1) : d23979 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d23979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, d23979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1165 q = 1) (hb : d208033 q = 1) : d23980 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d23980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1165, d23980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1166 q = 1) (hb : d208033 q = 1) : d23981 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d23981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d23981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1167 q = 1) (hb : d208033 q = 1) : d23982 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d23982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d23982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1168 q = 1) (hb : d208033 q = 1) : d23983 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1168, d23983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1168, d23983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56154 (p : Pattern) (ha : d1171 p = 1) (hb : d208033 p = 1) : d23986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d208033 q = 1) : d23964 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d23964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56149 q ha hb
    | true =>
      simp only [d1149, d23964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d208033 q = 1) : d23965 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d23965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d23965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d208033 q = 1) : d23968 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56150 q ha hb
    | true =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d208033 q = 1) : d23969 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d208033 q = 1) : d23970 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d23970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d23970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d208033 q = 1) : d23971 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d23971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1156, d23971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1157 q = 1) (hb : d208033 q = 1) : d23972 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1157, d23972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1157, d23972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1171 q = 1) (hb : d208033 q = 1) : d23986 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1171, d23986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1171, d23986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56155 (p : Pattern) (ha : d1172 p = 1) (hb : d208033 p = 1) : d23987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d208033 q = 1) : d23968 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56150 q ha hb
    | true =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d208033 q = 1) : d23969 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d208033 q = 1) : d23974 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d23974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d23974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d208033 q = 1) : d23975 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d23975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d23975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1161 q = 1) (hb : d208033 q = 1) : d23976 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, d23976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1161, d23976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1172 q = 1) (hb : d208033 q = 1) : d23987 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1172, d23987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1172, d23987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56156 (p : Pattern) (ha : d1178 p = 1) (hb : d208033 p = 1) : d23993 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1163 q = 1) (hb : d208033 q = 1) : d23978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d23978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56151 q ha hb
    | true =>
      simp only [d1163, d23978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56152 q ha hb
  have h2 (q : Pattern) (ha : d1164 q = 1) (hb : d208033 q = 1) : d23979 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d23979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, d23979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1165 q = 1) (hb : d208033 q = 1) : d23980 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d23980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1165, d23980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1166 q = 1) (hb : d208033 q = 1) : d23981 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d23981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d23981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1167 q = 1) (hb : d208033 q = 1) : d23982 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d23982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d23982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1173 q = 1) (hb : d208033 q = 1) : d23988 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d23988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56154 q ha hb
    | true =>
      simp only [d1173, d23988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56155 q ha hb
  have h7 (q : Pattern) (ha : d1174 q = 1) (hb : d208033 q = 1) : d23989 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d23989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1174, d23989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1175 q = 1) (hb : d208033 q = 1) : d23990 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d23990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1175, d23990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1176 q = 1) (hb : d208033 q = 1) : d23991 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d23991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, d23991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1177 q = 1) (hb : d208033 q = 1) : d23992 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d23992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, d23992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1178 q = 1) (hb : d208033 q = 1) : d23993 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1178, d23993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1178, d23993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56157 (p : Pattern) (ha : d1355 p = 1) (hb : d208033 p = 1) : d24140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1163 q = 1) (hb : d208033 q = 1) : d23978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d23978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56151 q ha hb
    | true =>
      simp only [d1163, d23978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56152 q ha hb
  have h2 (q : Pattern) (ha : d1164 q = 1) (hb : d208033 q = 1) : d23979 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d23979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, d23979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1165 q = 1) (hb : d208033 q = 1) : d23980 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d23980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1165, d23980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1166 q = 1) (hb : d208033 q = 1) : d23981 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d23981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d23981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1167 q = 1) (hb : d208033 q = 1) : d23982 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d23982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d23982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1350 q = 1) (hb : d208033 q = 1) : d24135 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d24135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56152 q ha hb
    | true =>
      simp only [d1350, d24135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1351 q = 1) (hb : d208033 q = 1) : d24136 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d24136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d24136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1352 q = 1) (hb : d208033 q = 1) : d24137 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d24137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1352, d24137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1353 q = 1) (hb : d208033 q = 1) : d24138 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d24138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d24138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1354 q = 1) (hb : d208033 q = 1) : d24139 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d24139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d24139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1355 q = 1) (hb : d208033 q = 1) : d24140 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1355, d24140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1355, d24140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56158 (p : Pattern) (ha : d1361 p = 1) (hb : d208033 p = 1) : d24146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1350 q = 1) (hb : d208033 q = 1) : d24135 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d24135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56152 q ha hb
    | true =>
      simp only [d1350, d24135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1351 q = 1) (hb : d208033 q = 1) : d24136 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d24136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d24136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1352 q = 1) (hb : d208033 q = 1) : d24137 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d24137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1352, d24137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1353 q = 1) (hb : d208033 q = 1) : d24138 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d24138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d24138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1354 q = 1) (hb : d208033 q = 1) : d24139 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d24139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d24139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1356 q = 1) (hb : d208033 q = 1) : d24141 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, d24141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56155 q ha hb
    | true =>
      simp only [d1356, d24141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1357 q = 1) (hb : d208033 q = 1) : d24142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d24142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, d24142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1358 q = 1) (hb : d208033 q = 1) : d24143 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d24143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1358, d24143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1359 q = 1) (hb : d208033 q = 1) : d24144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, d24144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, d24144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1360 q = 1) (hb : d208033 q = 1) : d24145 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, d24145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, d24145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1361 q = 1) (hb : d208033 q = 1) : d24146 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1361, d24146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1361, d24146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56159 (p : Pattern) (ha : d1370 p = 1) (hb : d208033 p = 1) : d24155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1356 q = 1) (hb : d208033 q = 1) : d24141 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, d24141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56155 q ha hb
    | true =>
      simp only [d1356, d24141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1357 q = 1) (hb : d208033 q = 1) : d24142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d24142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, d24142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1358 q = 1) (hb : d208033 q = 1) : d24143 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d24143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1358, d24143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1359 q = 1) (hb : d208033 q = 1) : d24144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, d24144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, d24144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1360 q = 1) (hb : d208033 q = 1) : d24145 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, d24145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, d24145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1370 q = 1) (hb : d208033 q = 1) : d24155 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1370, d24155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1370, d24155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56160 (p : Pattern) (ha : d1401 p = 1) (hb : d208033 p = 1) : d24186 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1385 q = 1) (hb : d208033 q = 1) : d24170 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d24170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d24170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56144 q ha hb
  have h2 (q : Pattern) (ha : d1110 q = 1) (hb : d208033 q = 1) : d23939 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d23939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56144 q ha hb
    | true =>
      simp only [d1110, d23939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1386 q = 1) (hb : d208033 q = 1) : d24171 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d24171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1386, d24171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1111 q = 1) (hb : d208033 q = 1) : d23940 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d23940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1111, d23940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1387 q = 1) (hb : d208033 q = 1) : d24172 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d24172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1387, d24172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1388 q = 1) (hb : d208033 q = 1) : d24173 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d24173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1388, d24173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1391 q = 1) (hb : d208033 q = 1) : d24176 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d24176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d24176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56145 q ha hb
  have h8 (q : Pattern) (ha : d1121 q = 1) (hb : d208033 q = 1) : d23945 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d23945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56145 q ha hb
    | true =>
      simp only [d1121, d23945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1392 q = 1) (hb : d208033 q = 1) : d24177 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d24177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1392, d24177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1122 q = 1) (hb : d208033 q = 1) : d23946 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d23946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1122, d23946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1393 q = 1) (hb : d208033 q = 1) : d24178 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d24178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1393, d24178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1394 q = 1) (hb : d208033 q = 1) : d24179 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d24179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1394, d24179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1395 q = 1) (hb : d208033 q = 1) : d24180 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d24180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1395, d24180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1400 q = 1) (hb : d208033 q = 1) : d24185 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d24185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1400, d24185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d1401 q = 1) (hb : d208033 q = 1) : d24186 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1401, d24186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1401, d24186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56161 (p : Pattern) (ha : d1411 p = 1) (hb : d208033 p = 1) : d24191 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1391 q = 1) (hb : d208033 q = 1) : d24176 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d24176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d24176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56145 q ha hb
  have h2 (q : Pattern) (ha : d1121 q = 1) (hb : d208033 q = 1) : d23945 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d23945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56145 q ha hb
    | true =>
      simp only [d1121, d23945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1392 q = 1) (hb : d208033 q = 1) : d24177 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d24177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1392, d24177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1122 q = 1) (hb : d208033 q = 1) : d23946 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d23946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1122, d23946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1393 q = 1) (hb : d208033 q = 1) : d24178 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d24178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1393, d24178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1394 q = 1) (hb : d208033 q = 1) : d24179 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d24179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1394, d24179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1400 q = 1) (hb : d208033 q = 1) : d24185 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d24185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1400, d24185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1410 q = 1) (hb : d208033 q = 1) : d1410 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1411 q = 1) (hb : d208033 q = 1) : d24191 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1411, d24191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1411, d24191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro56162 (p : Pattern) (ha : d1430 p = 1) (hb : d208033 p = 1) : d24210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1412 q = 1) (hb : d208033 q = 1) : d24192 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d24192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56160 q ha hb
    | true =>
      simp only [d1412, d24192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56161 q ha hb
  have h2 (q : Pattern) (ha : d1413 q = 1) (hb : d208033 q = 1) : d24193 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d24193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d24193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1414 q = 1) (hb : d208033 q = 1) : d24194 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d24194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d24194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1420 q = 1) (hb : d208033 q = 1) : d24200 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d24200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1420, d24200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1429 q = 1) (hb : d208033 q = 1) : d24209 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1429, d24209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1429, d24209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1430 q = 1) (hb : d208033 q = 1) : d24210 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1430, d24210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1430, d24210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56163 (p : Pattern) (ha : d1497 p = 1) (hb : d208033 p = 1) : d24285 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1431 q = 1) (hb : d208033 q = 1) : d24211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d24211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56162 q ha hb
    | true =>
      simp only [d1431, d24211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1432 q = 1) (hb : d208033 q = 1) : d24212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d24212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d24212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1494 q = 1) (hb : d208033 q = 1) : d24282 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1494, d24282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1494, d24282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1495 q = 1) (hb : d208033 q = 1) : d24283 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1495, d24283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1495, d24283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1496 q = 1) (hb : d208033 q = 1) : d24284 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1496, d24284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1496, d24284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1497 q = 1) (hb : d208033 q = 1) : d24285 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1497, d24285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1497, d24285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56164 (p : Pattern) (ha : d1503 p = 1) (hb : d208033 p = 1) : d24291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1498 q = 1) (hb : d208033 q = 1) : d24286 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1498, d24286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56163 q ha hb
    | true =>
      simp only [d1498, d24286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1499 q = 1) (hb : d208033 q = 1) : d24287 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1499, d24287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1499, d24287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1500 q = 1) (hb : d208033 q = 1) : d24288 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1500, d24288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1500, d24288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1501 q = 1) (hb : d208033 q = 1) : d24289 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1501, d24289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1501, d24289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1502 q = 1) (hb : d208033 q = 1) : d24290 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1502, d24290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1502, d24290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1503 q = 1) (hb : d208033 q = 1) : d24291 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1503, d24291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1503, d24291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56165 (p : Pattern) (ha : d1183 p = 1) (hb : d208033 p = 1) : d23998 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d208033 q = 1) : d23964 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d23964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56149 q ha hb
    | true =>
      simp only [d1149, d23964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d208033 q = 1) : d23965 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d23965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d23965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d208033 q = 1) : d23968 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56150 q ha hb
    | true =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d208033 q = 1) : d23969 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d208033 q = 1) : d23970 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d23970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d23970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d208033 q = 1) : d23971 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d23971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1156, d23971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1182 q = 1) (hb : d208033 q = 1) : d23997 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1182, d23997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1182, d23997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1183 q = 1) (hb : d208033 q = 1) : d23998 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1183, d23998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1183, d23998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56166 (p : Pattern) (ha : d1185 p = 1) (hb : d208033 p = 1) : d24000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d208033 q = 1) : d23968 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56150 q ha hb
    | true =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d208033 q = 1) : d23969 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d208033 q = 1) : d23974 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d23974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d23974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d208033 q = 1) : d23975 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d23975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d23975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1184 q = 1) (hb : d208033 q = 1) : d23999 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d23999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, d23999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1185 q = 1) (hb : d208033 q = 1) : d24000 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1185, d24000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1185, d24000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56167 (p : Pattern) (ha : d1192 p = 1) (hb : d208033 p = 1) : d24007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d208033 q = 1) : d23964 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d23964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56149 q ha hb
    | true =>
      simp only [d1149, d23964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d208033 q = 1) : d23965 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d23965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d23965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d208033 q = 1) : d23968 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56150 q ha hb
    | true =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d208033 q = 1) : d23969 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d208033 q = 1) : d23970 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d23970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d23970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1190 q = 1) (hb : d208033 q = 1) : d24005 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1190, d24005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1190, d24005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1191 q = 1) (hb : d208033 q = 1) : d24006 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1191, d24006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1191, d24006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1192 q = 1) (hb : d208033 q = 1) : d24007 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1192, d24007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1192, d24007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56168 (p : Pattern) (ha : d1195 p = 1) (hb : d208033 p = 1) : d24010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d208033 q = 1) : d23968 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56150 q ha hb
    | true =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d208033 q = 1) : d23969 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d208033 q = 1) : d23974 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d23974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d23974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1193 q = 1) (hb : d208033 q = 1) : d24008 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d24008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, d24008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1194 q = 1) (hb : d208033 q = 1) : d24009 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, d24009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1194, d24009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d208033 q = 1) : d24010 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1195, d24010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1195, d24010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56169 (p : Pattern) (ha : d1209 p = 1) (hb : d208033 p = 1) : d24016 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1202 q = 1) : d1202 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1206 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1207 q = 1) (hb : d208033 q = 1) : d24014 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1207, d208033, d24014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1207, d208033, d24014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1208 q = 1) (hb : d208033 q = 1) : d24015 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1208, d24015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1208, d24015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d1090 q = 1) : d1090 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d830 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1091 q = 1) (hb : d208033 q = 1) : d23927 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1091, d208033, d23927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1091, d208033, d23927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1092 q = 1) (hb : d208033 q = 1) : d23928 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1092, d23928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1092, d23928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d1209 q = 1) (hb : d208033 q = 1) : d24016 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1209, d24016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1209, d24016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro56170 (p : Pattern) (ha : d1215 p = 1) (hb : d208033 p = 1) : d24022 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1210 q = 1) (hb : d208033 q = 1) : d24017 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d24017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56169 q ha hb
    | true =>
      simp only [d1210, d24017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1211 q = 1) (hb : d208033 q = 1) : d24018 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d24018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1211, d24018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1212 q = 1) (hb : d208033 q = 1) : d24019 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1212, d24019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1212, d24019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1213 q = 1) (hb : d208033 q = 1) : d24020 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1213, d24020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1213, d24020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1100 q = 1) (hb : d208033 q = 1) : d23932 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d23932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56143 q ha hb
    | true =>
      simp only [d1100, d23932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1101 q = 1) (hb : d208033 q = 1) : d23933 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d23933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1101, d23933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1102 q = 1) (hb : d208033 q = 1) : d23934 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d23934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1102, d23934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1103 q = 1) (hb : d208033 q = 1) : d23935 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d23935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1103, d23935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1214 q = 1) (hb : d208033 q = 1) : d24021 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1214, d24021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1214, d24021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1110 q = 1) (hb : d208033 q = 1) : d23939 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d23939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56144 q ha hb
    | true =>
      simp only [d1110, d23939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1111 q = 1) (hb : d208033 q = 1) : d23940 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d23940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1111, d23940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1112 q = 1) (hb : d208033 q = 1) : d23941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d23941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d23941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1113 q = 1) (hb : d208033 q = 1) : d23942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d23942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1113, d23942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d1114 q = 1) (hb : d208033 q = 1) : d23943 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1114, d23943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1114, d23943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1215 q = 1) (hb : d208033 q = 1) : d24022 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1215, d24022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1215, d24022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56171 (p : Pattern) (ha : d1221 p = 1) (hb : d208033 p = 1) : d24028 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1216 q = 1) (hb : d208033 q = 1) : d24023 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1216, d24023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56170 q ha hb
    | true =>
      simp only [d1216, d24023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56146 q ha hb
  have h2 (q : Pattern) (ha : d1217 q = 1) (hb : d208033 q = 1) : d24024 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1217, d24024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1217, d24024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1218 q = 1) (hb : d208033 q = 1) : d24025 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1218, d24025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1218, d24025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1129 q = 1) (hb : d208033 q = 1) : d23953 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d23953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56146 q ha hb
    | true =>
      simp only [d1129, d23953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56147 q ha hb
  have h5 (q : Pattern) (ha : d1130 q = 1) (hb : d208033 q = 1) : d23954 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d23954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d23954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1131 q = 1) (hb : d208033 q = 1) : d23955 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d23955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d23955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1219 q = 1) (hb : d208033 q = 1) : d24026 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1219, d24026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1219, d24026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1142 q = 1) (hb : d208033 q = 1) : d23957 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d23957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56147 q ha hb
    | true =>
      simp only [d1142, d23957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56148 q ha hb
  have h9 (q : Pattern) (ha : d1143 q = 1) (hb : d208033 q = 1) : d23958 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d23958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d23958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1144 q = 1) (hb : d208033 q = 1) : d23959 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d23959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d23959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1145 q = 1) (hb : d208033 q = 1) : d23960 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, d23960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1145, d23960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1220 q = 1) (hb : d208033 q = 1) : d24027 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1220, d24027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1220, d24027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1221 q = 1) (hb : d208033 q = 1) : d24028 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1221, d24028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1221, d24028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro56172 (p : Pattern) (ha : d1227 p = 1) (hb : d208033 p = 1) : d24034 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1222 q = 1) (hb : d208033 q = 1) : d24029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, d24029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56171 q ha hb
    | true =>
      simp only [d1222, d24029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1223 q = 1) (hb : d208033 q = 1) : d24030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1223, d24030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1223, d24030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1149 q = 1) (hb : d208033 q = 1) : d23964 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d23964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56149 q ha hb
    | true =>
      simp only [d1149, d23964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1150 q = 1) (hb : d208033 q = 1) : d23965 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d23965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d23965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1224 q = 1) (hb : d208033 q = 1) : d24031 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1224, d24031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1224, d24031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1225 q = 1) (hb : d208033 q = 1) : d24032 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1225, d24032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1225, d24032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1226 q = 1) (hb : d208033 q = 1) : d24033 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1226, d24033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1226, d24033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1227 q = 1) (hb : d208033 q = 1) : d24034 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1227, d24034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1227, d24034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56173 (p : Pattern) (ha : d5545 p = 1) (hb : d208033 p = 1) : d24091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1110 q = 1) (hb : d208033 q = 1) : d23939 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d23939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56144 q ha hb
    | true =>
      simp only [d1110, d23939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1111 q = 1) (hb : d208033 q = 1) : d23940 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d23940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1111, d23940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1112 q = 1) (hb : d208033 q = 1) : d23941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d23941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d23941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1113 q = 1) (hb : d208033 q = 1) : d23942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d23942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1113, d23942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1121 q = 1) (hb : d208033 q = 1) : d23945 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d23945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56145 q ha hb
    | true =>
      simp only [d1121, d23945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1122 q = 1) (hb : d208033 q = 1) : d23946 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d23946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1122, d23946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1123 q = 1) (hb : d208033 q = 1) : d23947 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d23947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d23947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1124 q = 1) (hb : d208033 q = 1) : d23948 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d23948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1124, d23948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1125 q = 1) (hb : d208033 q = 1) : d23949 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d23949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1125, d23949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5544 q = 1) (hb : d208033 q = 1) : d5544 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5545 q = 1) (hb : d208033 q = 1) : d24091 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5545, d24091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5545, d24091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56174 (p : Pattern) (ha : d5552 p = 1) (hb : d208033 p = 1) : d24097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1129 q = 1) (hb : d208033 q = 1) : d23953 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d23953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56146 q ha hb
    | true =>
      simp only [d1129, d23953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56147 q ha hb
  have h2 (q : Pattern) (ha : d1130 q = 1) (hb : d208033 q = 1) : d23954 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d23954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d23954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1131 q = 1) (hb : d208033 q = 1) : d23955 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d23955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d23955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1142 q = 1) (hb : d208033 q = 1) : d23957 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d23957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56147 q ha hb
    | true =>
      simp only [d1142, d23957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56148 q ha hb
  have h5 (q : Pattern) (ha : d1143 q = 1) (hb : d208033 q = 1) : d23958 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d23958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d23958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1144 q = 1) (hb : d208033 q = 1) : d23959 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d23959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d23959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1145 q = 1) (hb : d208033 q = 1) : d23960 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, d23960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1145, d23960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5546 q = 1) (hb : d208033 q = 1) : d5546 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d5547 q = 1) (hb : d208033 q = 1) : d24092 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5547, d24092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56173 q ha hb
    | true =>
      simp only [d5547, d24092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5548 q = 1) (hb : d208033 q = 1) : d24093 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5548, d24093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5548, d24093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5549 q = 1) (hb : d208033 q = 1) : d24094 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5549, d24094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5549, d24094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5550 q = 1) (hb : d208033 q = 1) : d24095 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5550, d24095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5550, d24095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5551 q = 1) (hb : d208033 q = 1) : d24096 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5551, d24096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5551, d24096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5552 q = 1) (hb : d208033 q = 1) : d24097 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5552, d24097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5552, d24097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro56175 (p : Pattern) (ha : d5558 p = 1) (hb : d208033 p = 1) : d24103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5553 q = 1) (hb : d208033 q = 1) : d24098 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5553, d24098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56174 q ha hb
    | true =>
      simp only [d5553, d24098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5554 q = 1) (hb : d208033 q = 1) : d24099 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5554, d24099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5554, d24099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5555 q = 1) (hb : d208033 q = 1) : d24100 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5555, d24100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5555, d24100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5556 q = 1) (hb : d208033 q = 1) : d24101 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5556, d24101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5556, d24101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5557 q = 1) (hb : d208033 q = 1) : d24102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5557, d24102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5557, d24102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5558 q = 1) (hb : d208033 q = 1) : d24103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5558, d24103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5558, d24103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56176 (p : Pattern) (ha : d74690 p = 1) (hb : d208033 p = 1) : d211244 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1186 q = 1) (hb : d208033 q = 1) : d24001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d24001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56165 q ha hb
    | true =>
      simp only [d1186, d24001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56166 q ha hb
  have h2 (q : Pattern) (ha : d1187 q = 1) (hb : d208033 q = 1) : d24002 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d24002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, d24002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1188 q = 1) (hb : d208033 q = 1) : d24003 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d24003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1188, d24003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1189 q = 1) (hb : d208033 q = 1) : d24004 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d24004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d24004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1196 q = 1) (hb : d208033 q = 1) : d24011 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d24011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56167 q ha hb
    | true =>
      simp only [d1196, d24011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56168 q ha hb
  have h6 (q : Pattern) (ha : d1197 q = 1) (hb : d208033 q = 1) : d24012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d24012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d24012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1198 q = 1) (hb : d208033 q = 1) : d24013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d24013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1198, d24013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1228 q = 1) (hb : d208033 q = 1) : d24035 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d24035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56172 q ha hb
    | true =>
      simp only [d1228, d24035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56151 q ha hb
  have h9 (q : Pattern) (ha : d4485 q = 1) (hb : d208033 q = 1) : d211240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d211240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4485, d211240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5559 q = 1) (hb : d208033 q = 1) : d24104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5559, d24104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56175 q ha hb
    | true =>
      simp only [d5559, d24104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5560 q = 1) (hb : d208033 q = 1) : d24105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5560, d24105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5560, d24105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74687 q = 1) (hb : d208033 q = 1) : d211241 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74687, d211241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74687, d211241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74688 q = 1) (hb : d208033 q = 1) : d211242 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74688, d211242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74688, d211242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74689 q = 1) (hb : d208033 q = 1) : d211243 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74689, d211243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74689, d211243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74690 q = 1) (hb : d208033 q = 1) : d211244 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74690, d211244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74690, d211244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56177 (p : Pattern) (ha : d1326 p = 1) (hb : d208033 p = 1) : d24110 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d208033 q = 1) : d23964 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d23964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56149 q ha hb
    | true =>
      simp only [d1149, d23964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d208033 q = 1) : d23965 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d23965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d23965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d208033 q = 1) : d23968 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56150 q ha hb
    | true =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d208033 q = 1) : d23969 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d208033 q = 1) : d23970 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d23970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d23970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d208033 q = 1) : d23971 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d23971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1156, d23971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1182 q = 1) (hb : d208033 q = 1) : d23997 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1182, d23997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1182, d23997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1326 q = 1) (hb : d208033 q = 1) : d24110 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1326, d24110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1326, d24110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56178 (p : Pattern) (ha : d1327 p = 1) (hb : d208033 p = 1) : d24111 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d208033 q = 1) : d23968 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56150 q ha hb
    | true =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d208033 q = 1) : d23969 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d208033 q = 1) : d23974 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d23974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d23974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d208033 q = 1) : d23975 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d23975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d23975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1184 q = 1) (hb : d208033 q = 1) : d23999 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d23999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, d23999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1327 q = 1) (hb : d208033 q = 1) : d24111 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1327, d24111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1327, d24111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56179 (p : Pattern) (ha : d1332 p = 1) (hb : d208033 p = 1) : d24116 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d208033 q = 1) : d23964 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d23964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56149 q ha hb
    | true =>
      simp only [d1149, d23964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d208033 q = 1) : d23965 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d23965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d23965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d208033 q = 1) : d23968 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56150 q ha hb
    | true =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d208033 q = 1) : d23969 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d208033 q = 1) : d23970 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d23970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d23970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1190 q = 1) (hb : d208033 q = 1) : d24005 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1190, d24005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1190, d24005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1191 q = 1) (hb : d208033 q = 1) : d24006 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1191, d24006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1191, d24006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1332 q = 1) (hb : d208033 q = 1) : d24116 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1332, d24116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1332, d24116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56180 (p : Pattern) (ha : d1333 p = 1) (hb : d208033 p = 1) : d24117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d208033 q = 1) : d23968 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56150 q ha hb
    | true =>
      simp only [d1153, d23968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d208033 q = 1) : d23969 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d23969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d208033 q = 1) : d23974 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d23974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d23974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1193 q = 1) (hb : d208033 q = 1) : d24008 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d24008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, d24008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1194 q = 1) (hb : d208033 q = 1) : d24009 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, d24009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1194, d24009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1333 q = 1) (hb : d208033 q = 1) : d24117 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1333, d24117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1333, d24117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56181 (p : Pattern) (ha : d1337 p = 1) (hb : d208033 p = 1) : d24121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1222 q = 1) (hb : d208033 q = 1) : d24029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, d24029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56171 q ha hb
    | true =>
      simp only [d1222, d24029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1223 q = 1) (hb : d208033 q = 1) : d24030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1223, d24030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1223, d24030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1149 q = 1) (hb : d208033 q = 1) : d23964 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d23964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56149 q ha hb
    | true =>
      simp only [d1149, d23964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1150 q = 1) (hb : d208033 q = 1) : d23965 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d23965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d23965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1224 q = 1) (hb : d208033 q = 1) : d24031 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1224, d24031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1224, d24031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1225 q = 1) (hb : d208033 q = 1) : d24032 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1225, d24032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1225, d24032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1226 q = 1) (hb : d208033 q = 1) : d24033 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1226, d24033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1226, d24033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1337 q = 1) (hb : d208033 q = 1) : d24121 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1337, d24121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1337, d24121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56182 (p : Pattern) (ha : d5565 p = 1) (hb : d208033 p = 1) : d24127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5553 q = 1) (hb : d208033 q = 1) : d24098 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5553, d24098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56174 q ha hb
    | true =>
      simp only [d5553, d24098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5554 q = 1) (hb : d208033 q = 1) : d24099 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5554, d24099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5554, d24099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5555 q = 1) (hb : d208033 q = 1) : d24100 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5555, d24100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5555, d24100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5556 q = 1) (hb : d208033 q = 1) : d24101 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5556, d24101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5556, d24101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5557 q = 1) (hb : d208033 q = 1) : d24102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5557, d24102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5557, d24102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5565 q = 1) (hb : d208033 q = 1) : d24127 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5565, d24127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5565, d24127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56183 (p : Pattern) (ha : d74694 p = 1) (hb : d208033 p = 1) : d211249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1186 q = 1) (hb : d208033 q = 1) : d24001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d24001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56165 q ha hb
    | true =>
      simp only [d1186, d24001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56166 q ha hb
  have h2 (q : Pattern) (ha : d1187 q = 1) (hb : d208033 q = 1) : d24002 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d24002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, d24002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1188 q = 1) (hb : d208033 q = 1) : d24003 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d24003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1188, d24003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1189 q = 1) (hb : d208033 q = 1) : d24004 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d24004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d24004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1196 q = 1) (hb : d208033 q = 1) : d24011 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d24011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56167 q ha hb
    | true =>
      simp only [d1196, d24011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56168 q ha hb
  have h6 (q : Pattern) (ha : d1197 q = 1) (hb : d208033 q = 1) : d24012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d24012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d24012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1198 q = 1) (hb : d208033 q = 1) : d24013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d24013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1198, d24013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1228 q = 1) (hb : d208033 q = 1) : d24035 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d24035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56172 q ha hb
    | true =>
      simp only [d1228, d24035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56151 q ha hb
  have h9 (q : Pattern) (ha : d4485 q = 1) (hb : d208033 q = 1) : d211240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d211240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4485, d211240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5559 q = 1) (hb : d208033 q = 1) : d24104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5559, d24104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56175 q ha hb
    | true =>
      simp only [d5559, d24104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5560 q = 1) (hb : d208033 q = 1) : d24105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5560, d24105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5560, d24105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74687 q = 1) (hb : d208033 q = 1) : d211241 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74687, d211241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74687, d211241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74688 q = 1) (hb : d208033 q = 1) : d211242 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74688, d211242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74688, d211242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74689 q = 1) (hb : d208033 q = 1) : d211243 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74689, d211243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74689, d211243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1328 q = 1) (hb : d208033 q = 1) : d24112 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1328, d24112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56177 q ha hb
    | true =>
      simp only [d1328, d24112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56178 q ha hb
  have h16 (q : Pattern) (ha : d1329 q = 1) (hb : d208033 q = 1) : d24113 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1329, d24113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1329, d24113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1330 q = 1) (hb : d208033 q = 1) : d24114 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1330, d24114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1330, d24114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d1331 q = 1) (hb : d208033 q = 1) : d24115 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1331, d24115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1331, d24115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1334 q = 1) (hb : d208033 q = 1) : d24118 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1334, d24118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56179 q ha hb
    | true =>
      simp only [d1334, d24118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56180 q ha hb
  have h20 (q : Pattern) (ha : d1335 q = 1) (hb : d208033 q = 1) : d24119 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1335, d24119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1335, d24119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d1336 q = 1) (hb : d208033 q = 1) : d24120 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1336, d24120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d1336, d24120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d1338 q = 1) (hb : d208033 q = 1) : d24122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d24122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56181 q ha hb
    | true =>
      simp only [d1338, d24122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56154 q ha hb
  have h23 (q : Pattern) (ha : d4490 q = 1) (hb : d208033 q = 1) : d211245 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d211245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4490, d211245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d5566 q = 1) (hb : d208033 q = 1) : d24128 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5566, d24128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56182 q ha hb
    | true =>
      simp only [d5566, d24128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d5567 q = 1) (hb : d208033 q = 1) : d24129 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5567, d24129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5567, d24129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d74691 q = 1) (hb : d208033 q = 1) : d211246 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74691, d211246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d74691, d211246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d74692 q = 1) (hb : d208033 q = 1) : d211247 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74692, d211247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74692, d211247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d74693 q = 1) (hb : d208033 q = 1) : d211248 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74693, d211248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74693, d211248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d74694 q = 1) (hb : d208033 q = 1) : d211249 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74694, d211249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74694, d211249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro56184 (p : Pattern) (ha : d74701 p = 1) (hb : d208033 p = 1) : d211256 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1338 q = 1) (hb : d208033 q = 1) : d24122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d24122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56181 q ha hb
    | true =>
      simp only [d1338, d24122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56154 q ha hb
  have h2 (q : Pattern) (ha : d4490 q = 1) (hb : d208033 q = 1) : d211245 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d211245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4490, d211245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5566 q = 1) (hb : d208033 q = 1) : d24128 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5566, d24128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56182 q ha hb
    | true =>
      simp only [d5566, d24128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5567 q = 1) (hb : d208033 q = 1) : d24129 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5567, d24129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5567, d24129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74691 q = 1) (hb : d208033 q = 1) : d211246 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74691, d211246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74691, d211246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74699 q = 1) (hb : d208033 q = 1) : d211254 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74699, d211254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74699, d211254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74700 q = 1) (hb : d208033 q = 1) : d211255 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74700, d211255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74700, d211255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74701 q = 1) (hb : d208033 q = 1) : d211256 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74701, d211256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74701, d211256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56185 (p : Pattern) (ha : d1390 p = 1) (hb : d208033 p = 1) : d24175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1376 q = 1) (hb : d208033 q = 1) : d24161 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1376, d24161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1376, d24161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56169 q ha hb
  have h2 (q : Pattern) (ha : d1210 q = 1) (hb : d208033 q = 1) : d24017 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d24017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56169 q ha hb
    | true =>
      simp only [d1210, d24017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1377 q = 1) (hb : d208033 q = 1) : d24162 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1377, d24162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1377, d24162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1211 q = 1) (hb : d208033 q = 1) : d24018 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d24018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1211, d24018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1378 q = 1) (hb : d208033 q = 1) : d24163 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1378, d24163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1378, d24163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1379 q = 1) (hb : d208033 q = 1) : d24164 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1379, d24164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1379, d24164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1380 q = 1) (hb : d208033 q = 1) : d24165 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d24165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1380, d24165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56143 q ha hb
  have h8 (q : Pattern) (ha : d1100 q = 1) (hb : d208033 q = 1) : d23932 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d23932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56143 q ha hb
    | true =>
      simp only [d1100, d23932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1381 q = 1) (hb : d208033 q = 1) : d24166 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d24166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1381, d24166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1101 q = 1) (hb : d208033 q = 1) : d23933 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d23933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1101, d23933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1382 q = 1) (hb : d208033 q = 1) : d24167 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d24167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1382, d24167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1383 q = 1) (hb : d208033 q = 1) : d24168 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d24168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1383, d24168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1384 q = 1) (hb : d208033 q = 1) : d24169 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1384, d24169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1384, d24169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1385 q = 1) (hb : d208033 q = 1) : d24170 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d24170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d24170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56144 q ha hb
  have h15 (q : Pattern) (ha : d1110 q = 1) (hb : d208033 q = 1) : d23939 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d23939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56144 q ha hb
    | true =>
      simp only [d1110, d23939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d1386 q = 1) (hb : d208033 q = 1) : d24171 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d24171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1386, d24171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1111 q = 1) (hb : d208033 q = 1) : d23940 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d23940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1111, d23940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d1387 q = 1) (hb : d208033 q = 1) : d24172 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d24172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1387, d24172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1388 q = 1) (hb : d208033 q = 1) : d24173 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d24173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d1388, d24173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d1389 q = 1) (hb : d208033 q = 1) : d24174 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1389, d24174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1389, d24174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d1390 q = 1) (hb : d208033 q = 1) : d24175 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1390, d24175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1390, d24175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro56186 (p : Pattern) (ha : d1396 p = 1) (hb : d208033 p = 1) : d24181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1380 q = 1) (hb : d208033 q = 1) : d24165 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d24165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1380, d24165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56143 q ha hb
  have h2 (q : Pattern) (ha : d1100 q = 1) (hb : d208033 q = 1) : d23932 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d23932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56143 q ha hb
    | true =>
      simp only [d1100, d23932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1381 q = 1) (hb : d208033 q = 1) : d24166 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d24166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1381, d24166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1101 q = 1) (hb : d208033 q = 1) : d23933 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d23933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1101, d23933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1382 q = 1) (hb : d208033 q = 1) : d24167 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d24167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1382, d24167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1383 q = 1) (hb : d208033 q = 1) : d24168 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d24168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1383, d24168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1385 q = 1) (hb : d208033 q = 1) : d24170 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d24170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d24170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56144 q ha hb
  have h8 (q : Pattern) (ha : d1110 q = 1) (hb : d208033 q = 1) : d23939 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d23939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56144 q ha hb
    | true =>
      simp only [d1110, d23939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1386 q = 1) (hb : d208033 q = 1) : d24171 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d24171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1386, d24171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1111 q = 1) (hb : d208033 q = 1) : d23940 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d23940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1111, d23940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1387 q = 1) (hb : d208033 q = 1) : d24172 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d24172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1387, d24172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1388 q = 1) (hb : d208033 q = 1) : d24173 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d24173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1388, d24173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1389 q = 1) (hb : d208033 q = 1) : d24174 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1389, d24174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1389, d24174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1391 q = 1) (hb : d208033 q = 1) : d24176 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d24176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d24176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56145 q ha hb
  have h15 (q : Pattern) (ha : d1121 q = 1) (hb : d208033 q = 1) : d23945 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d23945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56145 q ha hb
    | true =>
      simp only [d1121, d23945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d1392 q = 1) (hb : d208033 q = 1) : d24177 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d24177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1392, d24177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1122 q = 1) (hb : d208033 q = 1) : d23946 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d23946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1122, d23946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d1393 q = 1) (hb : d208033 q = 1) : d24178 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d24178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1393, d24178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1394 q = 1) (hb : d208033 q = 1) : d24179 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d24179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d1394, d24179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d1395 q = 1) (hb : d208033 q = 1) : d24180 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d24180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1395, d24180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d1396 q = 1) (hb : d208033 q = 1) : d24181 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1396, d24181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1396, d24181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro56187 (p : Pattern) (ha : d1417 p = 1) (hb : d208033 p = 1) : d24197 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1397 q = 1) (hb : d208033 q = 1) : d24182 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1397, d24182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56185 q ha hb
    | true =>
      simp only [d1397, d24182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56186 q ha hb
  have h2 (q : Pattern) (ha : d1398 q = 1) (hb : d208033 q = 1) : d24183 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1398, d24183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1398, d24183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1399 q = 1) (hb : d208033 q = 1) : d24184 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1399, d24184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1399, d24184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1402 q = 1) (hb : d208033 q = 1) : d24187 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d24187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56186 q ha hb
    | true =>
      simp only [d1402, d24187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56160 q ha hb
  have h5 (q : Pattern) (ha : d1403 q = 1) (hb : d208033 q = 1) : d24188 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d24188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d24188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1404 q = 1) (hb : d208033 q = 1) : d24189 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d24189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d24189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1405 q = 1) (hb : d208033 q = 1) : d24190 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1405, d24190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1405, d24190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1412 q = 1) (hb : d208033 q = 1) : d24192 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d24192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56160 q ha hb
    | true =>
      simp only [d1412, d24192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56161 q ha hb
  have h9 (q : Pattern) (ha : d1413 q = 1) (hb : d208033 q = 1) : d24193 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d24193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d24193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1414 q = 1) (hb : d208033 q = 1) : d24194 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d24194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d24194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1415 q = 1) (hb : d208033 q = 1) : d24195 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d24195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1415, d24195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1416 q = 1) (hb : d208033 q = 1) : d24196 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1416, d24196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1416, d24196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1417 q = 1) (hb : d208033 q = 1) : d24197 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1417, d24197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1417, d24197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro56188 (p : Pattern) (ha : d1422 p = 1) (hb : d208033 p = 1) : d24202 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1402 q = 1) (hb : d208033 q = 1) : d24187 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d24187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56186 q ha hb
    | true =>
      simp only [d1402, d24187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56160 q ha hb
  have h2 (q : Pattern) (ha : d1403 q = 1) (hb : d208033 q = 1) : d24188 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d24188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d24188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1404 q = 1) (hb : d208033 q = 1) : d24189 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d24189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d24189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1412 q = 1) (hb : d208033 q = 1) : d24192 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d24192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56160 q ha hb
    | true =>
      simp only [d1412, d24192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56161 q ha hb
  have h5 (q : Pattern) (ha : d1413 q = 1) (hb : d208033 q = 1) : d24193 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d24193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d24193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1414 q = 1) (hb : d208033 q = 1) : d24194 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d24194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d24194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1415 q = 1) (hb : d208033 q = 1) : d24195 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d24195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1415, d24195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1420 q = 1) (hb : d208033 q = 1) : d24200 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d24200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1420, d24200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1421 q = 1) (hb : d208033 q = 1) : d24201 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1421, d24201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1421, d24201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1422 q = 1) (hb : d208033 q = 1) : d24202 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1422, d24202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1422, d24202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro56189 (p : Pattern) (ha : d1428 p = 1) (hb : d208033 p = 1) : d24208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1418 q = 1) (hb : d208033 q = 1) : d24198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1418, d24198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56187 q ha hb
    | true =>
      simp only [d1418, d24198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1419 q = 1) (hb : d208033 q = 1) : d24199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1419, d24199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1419, d24199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1423 q = 1) (hb : d208033 q = 1) : d24203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1423, d24203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56188 q ha hb
    | true =>
      simp only [d1423, d24203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1424 q = 1) (hb : d208033 q = 1) : d24204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1424, d24204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1424, d24204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1425 q = 1) (hb : d208033 q = 1) : d24205 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1425, d24205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1425, d24205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1426 q = 1) (hb : d208033 q = 1) : d24206 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1426, d24206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1426, d24206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1427 q = 1) (hb : d208033 q = 1) : d24207 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1427, d24207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1427, d24207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1428 q = 1) (hb : d208033 q = 1) : d24208 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1428, d24208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1428, d24208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56190 (p : Pattern) (ha : d1436 p = 1) (hb : d208033 p = 1) : d24216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1423 q = 1) (hb : d208033 q = 1) : d24203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1423, d24203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56188 q ha hb
    | true =>
      simp only [d1423, d24203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1424 q = 1) (hb : d208033 q = 1) : d24204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1424, d24204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1424, d24204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1431 q = 1) (hb : d208033 q = 1) : d24211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d24211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56162 q ha hb
    | true =>
      simp only [d1431, d24211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d208033 q = 1) : d24212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d24212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d24212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1433 q = 1) (hb : d208033 q = 1) : d24213 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1433, d24213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1433, d24213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1434 q = 1) (hb : d208033 q = 1) : d24214 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1434, d24214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1434, d24214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1435 q = 1) (hb : d208033 q = 1) : d24215 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1435, d24215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1435, d24215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1436 q = 1) (hb : d208033 q = 1) : d24216 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1436, d24216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1436, d24216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56191 (p : Pattern) (ha : d5589 p = 1) (hb : d208033 p = 1) : d24262 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1385 q = 1) (hb : d208033 q = 1) : d24170 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d24170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d24170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56144 q ha hb
  have h2 (q : Pattern) (ha : d1110 q = 1) (hb : d208033 q = 1) : d23939 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d23939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56144 q ha hb
    | true =>
      simp only [d1110, d23939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1386 q = 1) (hb : d208033 q = 1) : d24171 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d24171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1386, d24171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1111 q = 1) (hb : d208033 q = 1) : d23940 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d23940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1111, d23940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1387 q = 1) (hb : d208033 q = 1) : d24172 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d24172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1387, d24172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1388 q = 1) (hb : d208033 q = 1) : d24173 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d24173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1388, d24173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1391 q = 1) (hb : d208033 q = 1) : d24176 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d24176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d24176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56145 q ha hb
  have h8 (q : Pattern) (ha : d1121 q = 1) (hb : d208033 q = 1) : d23945 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d23945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56145 q ha hb
    | true =>
      simp only [d1121, d23945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1392 q = 1) (hb : d208033 q = 1) : d24177 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d24177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1392, d24177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1122 q = 1) (hb : d208033 q = 1) : d23946 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d23946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1122, d23946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1393 q = 1) (hb : d208033 q = 1) : d24178 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d24178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1393, d24178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1394 q = 1) (hb : d208033 q = 1) : d24179 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d24179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1394, d24179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1395 q = 1) (hb : d208033 q = 1) : d24180 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d24180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1395, d24180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5588 q = 1) (hb : d208033 q = 1) : d5588 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d5589 q = 1) (hb : d208033 q = 1) : d24262 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5589, d24262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5589, d24262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56192 (p : Pattern) (ha : d5596 p = 1) (hb : d208033 p = 1) : d24268 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1402 q = 1) (hb : d208033 q = 1) : d24187 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d24187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56186 q ha hb
    | true =>
      simp only [d1402, d24187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56160 q ha hb
  have h2 (q : Pattern) (ha : d1403 q = 1) (hb : d208033 q = 1) : d24188 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d24188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d24188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1404 q = 1) (hb : d208033 q = 1) : d24189 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d24189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d24189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1412 q = 1) (hb : d208033 q = 1) : d24192 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d24192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56160 q ha hb
    | true =>
      simp only [d1412, d24192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56161 q ha hb
  have h5 (q : Pattern) (ha : d1413 q = 1) (hb : d208033 q = 1) : d24193 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d24193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d24193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1414 q = 1) (hb : d208033 q = 1) : d24194 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d24194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d24194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1415 q = 1) (hb : d208033 q = 1) : d24195 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d24195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1415, d24195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5590 q = 1) (hb : d208033 q = 1) : d5590 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d5591 q = 1) (hb : d208033 q = 1) : d24263 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5591, d24263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56191 q ha hb
    | true =>
      simp only [d5591, d24263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5592 q = 1) (hb : d208033 q = 1) : d24264 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5592, d24264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5592, d24264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5593 q = 1) (hb : d208033 q = 1) : d24265 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5593, d24265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5593, d24265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5594 q = 1) (hb : d208033 q = 1) : d24266 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5594, d24266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5594, d24266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5595 q = 1) (hb : d208033 q = 1) : d24267 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5595, d24267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5595, d24267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5596 q = 1) (hb : d208033 q = 1) : d24268 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5596, d24268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5596, d24268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro56193 (p : Pattern) (ha : d5602 p = 1) (hb : d208033 p = 1) : d24274 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5597 q = 1) (hb : d208033 q = 1) : d24269 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5597, d24269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56192 q ha hb
    | true =>
      simp only [d5597, d24269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5598 q = 1) (hb : d208033 q = 1) : d24270 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5598, d24270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5598, d24270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5599 q = 1) (hb : d208033 q = 1) : d24271 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5599, d24271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5599, d24271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5600 q = 1) (hb : d208033 q = 1) : d24272 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5600, d24272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5600, d24272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5601 q = 1) (hb : d208033 q = 1) : d24273 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5601, d24273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5601, d24273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5602 q = 1) (hb : d208033 q = 1) : d24274 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5602, d24274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5602, d24274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56194 (p : Pattern) (ha : d74710 p = 1) (hb : d208033 p = 1) : d211266 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1437 q = 1) (hb : d208033 q = 1) : d24217 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1437, d24217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56189 q ha hb
    | true =>
      simp only [d1437, d24217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56190 q ha hb
  have h2 (q : Pattern) (ha : d4505 q = 1) (hb : d208033 q = 1) : d211262 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4505, d211262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4505, d211262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5603 q = 1) (hb : d208033 q = 1) : d24275 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5603, d24275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56193 q ha hb
    | true =>
      simp only [d5603, d24275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5604 q = 1) (hb : d208033 q = 1) : d24276 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5604, d24276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5604, d24276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74707 q = 1) (hb : d208033 q = 1) : d211263 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74707, d211263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74707, d211263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74708 q = 1) (hb : d208033 q = 1) : d211264 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74708, d211264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74708, d211264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74709 q = 1) (hb : d208033 q = 1) : d211265 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74709, d211265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74709, d211265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74710 q = 1) (hb : d208033 q = 1) : d211266 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74710, d211266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74710, d211266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56195 (p : Pattern) (ha : d74716 p = 1) (hb : d208033 p = 1) : d211272 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d208033 q = 1) : d23984 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d23984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d23984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56153 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d208033 q = 1) : d23985 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d23985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, d23985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d208033 q = 1) : d23994 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d23994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56153 q ha hb
    | true =>
      simp only [d1179, d23994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56156 q ha hb
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d208033 q = 1) : d23995 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d23995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, d23995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1181 q = 1) (hb : d208033 q = 1) : d23996 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d23996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, d23996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74695 q = 1) (hb : d208033 q = 1) : d211250 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74695, d211250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56176 q ha hb
    | true =>
      simp only [d74695, d211250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56183 q ha hb
  have h7 (q : Pattern) (ha : d1362 q = 1) (hb : d208033 q = 1) : d24147 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, d24147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56157 q ha hb
    | true =>
      simp only [d1362, d24147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56158 q ha hb
  have h8 (q : Pattern) (ha : d74696 q = 1) (hb : d208033 q = 1) : d211251 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74696, d211251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74696, d211251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74697 q = 1) (hb : d208033 q = 1) : d211252 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74697, d211252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74697, d211252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d74698 q = 1) (hb : d208033 q = 1) : d211253 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74698, d211253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74698, d211253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74702 q = 1) (hb : d208033 q = 1) : d211257 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74702, d211257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74702, d211257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56184 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d208033 q = 1) : d24156 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d24156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, d24156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56159 q ha hb
  have h13 (q : Pattern) (ha : d74703 q = 1) (hb : d208033 q = 1) : d211258 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74703, d211258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74703, d211258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74704 q = 1) (hb : d208033 q = 1) : d211259 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74704, d211259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74704, d211259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d74705 q = 1) (hb : d208033 q = 1) : d211260 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74705, d211260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74705, d211260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d74706 q = 1) (hb : d208033 q = 1) : d211261 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74706, d211261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74706, d211261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74711 q = 1) (hb : d208033 q = 1) : d211267 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74711, d211267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74711, d211267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56194 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d208033 q = 1) : d24292 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, d24292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, d24292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56164 q ha hb
  have h19 (q : Pattern) (ha : d74712 q = 1) (hb : d208033 q = 1) : d211268 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74712, d211268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74712, d211268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d74713 q = 1) (hb : d208033 q = 1) : d211269 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74713, d211269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74713, d211269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d74714 q = 1) (hb : d208033 q = 1) : d211270 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74714, d211270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74714, d211270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d74715 q = 1) (hb : d208033 q = 1) : d211271 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74715, d211271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74715, d211271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d74716 q = 1) (hb : d208033 q = 1) : d211272 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74716, d211272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74716, d211272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro56196 (p : Pattern) (ha : d74722 p = 1) (hb : d208033 p = 1) : d211278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74717 q = 1) (hb : d208033 q = 1) : d211273 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74717, d211273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74717, d211273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56195 q ha hb
  have h2 (q : Pattern) (ha : d74718 q = 1) (hb : d208033 q = 1) : d211274 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74718, d211274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74718, d211274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74719 q = 1) (hb : d208033 q = 1) : d211275 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74719, d211275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74719, d211275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74720 q = 1) (hb : d208033 q = 1) : d211276 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74720, d211276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74720, d211276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74721 q = 1) (hb : d208033 q = 1) : d211277 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74721, d211277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74721, d211277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74722 q = 1) (hb : d208033 q = 1) : d211278 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74722, d211278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74722, d211278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56197 (p : Pattern) (ha : d1554 p = 1) (hb : d208033 p = 1) : d24311 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1530 q = 1) : d1530 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1536 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1537 q = 1) (hb : d208033 q = 1) : d24307 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1537, d208033, d24307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1537, d208033, d24307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1538 q = 1) (hb : d208033 q = 1) : d24308 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1538, d24308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1538, d24308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d1546 q = 1) : d1546 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1551 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1552 q = 1) (hb : d208033 q = 1) : d24309 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1552, d208033, d24309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1552, d208033, d24309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1553 q = 1) (hb : d208033 q = 1) : d24310 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1553, d24310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1553, d24310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d1554 q = 1) (hb : d208033 q = 1) : d24311 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1554, d24311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1554, d24311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro56198 (p : Pattern) (ha : d1569 p = 1) (hb : d208033 p = 1) : d24318 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1546 q = 1) : d1546 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1551 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1552 q = 1) (hb : d208033 q = 1) : d24309 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1552, d208033, d24309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1552, d208033, d24309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1553 q = 1) (hb : d208033 q = 1) : d24310 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1553, d24310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1553, d24310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d1562 q = 1) : d1562 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1566 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1567 q = 1) (hb : d208033 q = 1) : d24316 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1567, d208033, d24316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1567, d208033, d24316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1568 q = 1) (hb : d208033 q = 1) : d24317 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1568, d24317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1568, d24317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d1569 q = 1) (hb : d208033 q = 1) : d24318 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1569, d24318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1569, d24318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro56199 (p : Pattern) (ha : d1581 p = 1) (hb : d208033 p = 1) : d24326 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1562 q = 1) : d1562 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1566 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1567 q = 1) (hb : d208033 q = 1) : d24316 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1567, d208033, d24316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1567, d208033, d24316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1568 q = 1) (hb : d208033 q = 1) : d24317 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1568, d24317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1568, d24317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d1577 q = 1) : d1577 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1578 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1579 q = 1) (hb : d208033 q = 1) : d24324 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1579, d208033, d24324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1579, d208033, d24324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1580 q = 1) (hb : d208033 q = 1) : d24325 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1580, d24325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1580, d24325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d1581 q = 1) (hb : d208033 q = 1) : d24326 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1581, d24326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1581, d24326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro56200 (p : Pattern) (ha : d1587 p = 1) (hb : d208033 p = 1) : d24332 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1555 q = 1) (hb : d208033 q = 1) : d24312 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d24312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56197 q ha hb
    | true =>
      simp only [d1555, d24312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1556 q = 1) (hb : d208033 q = 1) : d24313 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d24313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1556, d24313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1557 q = 1) (hb : d208033 q = 1) : d24314 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d24314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1557, d24314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1558 q = 1) (hb : d208033 q = 1) : d24315 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d24315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1558, d24315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1570 q = 1) (hb : d208033 q = 1) : d24319 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d24319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56198 q ha hb
    | true =>
      simp only [d1570, d24319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1571 q = 1) (hb : d208033 q = 1) : d24320 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d24320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1571, d24320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1572 q = 1) (hb : d208033 q = 1) : d24321 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d24321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d24321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1573 q = 1) (hb : d208033 q = 1) : d24322 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d24322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1573, d24322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1574 q = 1) (hb : d208033 q = 1) : d24323 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1574, d24323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1574, d24323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1582 q = 1) (hb : d208033 q = 1) : d24327 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d24327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56199 q ha hb
    | true =>
      simp only [d1582, d24327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1583 q = 1) (hb : d208033 q = 1) : d24328 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d24328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1583, d24328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1584 q = 1) (hb : d208033 q = 1) : d24329 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d24329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d24329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1585 q = 1) (hb : d208033 q = 1) : d24330 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d24330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1585, d24330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d1586 q = 1) (hb : d208033 q = 1) : d24331 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1586, d24331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1586, d24331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1587 q = 1) (hb : d208033 q = 1) : d24332 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1587, d24332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1587, d24332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56201 (p : Pattern) (ha : d1589 p = 1) (hb : d208033 p = 1) : d24334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1570 q = 1) (hb : d208033 q = 1) : d24319 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d24319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56198 q ha hb
    | true =>
      simp only [d1570, d24319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1571 q = 1) (hb : d208033 q = 1) : d24320 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d24320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1571, d24320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1572 q = 1) (hb : d208033 q = 1) : d24321 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d24321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d24321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1573 q = 1) (hb : d208033 q = 1) : d24322 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d24322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1573, d24322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1582 q = 1) (hb : d208033 q = 1) : d24327 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d24327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56199 q ha hb
    | true =>
      simp only [d1582, d24327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1583 q = 1) (hb : d208033 q = 1) : d24328 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d24328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1583, d24328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1584 q = 1) (hb : d208033 q = 1) : d24329 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d24329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d24329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1585 q = 1) (hb : d208033 q = 1) : d24330 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d24330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1585, d24330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1586 q = 1) (hb : d208033 q = 1) : d24331 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1586, d24331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1586, d24331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1588 q = 1) (hb : d208033 q = 1) : d24333 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, d24333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1588, d24333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1589 q = 1) (hb : d208033 q = 1) : d24334 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1589, d24334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1589, d24334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56202 (p : Pattern) (ha : d1602 p = 1) (hb : d208033 p = 1) : d24338 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1582 q = 1) (hb : d208033 q = 1) : d24327 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d24327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56199 q ha hb
    | true =>
      simp only [d1582, d24327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1583 q = 1) (hb : d208033 q = 1) : d24328 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d24328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1583, d24328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1584 q = 1) (hb : d208033 q = 1) : d24329 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d24329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d24329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1585 q = 1) (hb : d208033 q = 1) : d24330 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d24330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1585, d24330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1588 q = 1) (hb : d208033 q = 1) : d24333 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, d24333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1588, d24333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1601 q = 1) (hb : d208033 q = 1) : d1601 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1602 q = 1) (hb : d208033 q = 1) : d24338 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1602, d24338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1602, d24338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro56203 (p : Pattern) (ha : d1609 p = 1) (hb : d208033 p = 1) : d24345 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1590 q = 1) (hb : d208033 q = 1) : d24335 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d24335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56200 q ha hb
    | true =>
      simp only [d1590, d24335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56201 q ha hb
  have h2 (q : Pattern) (ha : d1591 q = 1) (hb : d208033 q = 1) : d24336 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d24336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d24336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1592 q = 1) (hb : d208033 q = 1) : d24337 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d24337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d24337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1603 q = 1) (hb : d208033 q = 1) : d24339 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d24339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56201 q ha hb
    | true =>
      simp only [d1603, d24339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56202 q ha hb
  have h5 (q : Pattern) (ha : d1604 q = 1) (hb : d208033 q = 1) : d24340 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d24340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d24340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1605 q = 1) (hb : d208033 q = 1) : d24341 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d24341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d24341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1606 q = 1) (hb : d208033 q = 1) : d24342 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, d24342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1606, d24342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1607 q = 1) (hb : d208033 q = 1) : d24343 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, d24343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1607, d24343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1608 q = 1) (hb : d208033 q = 1) : d24344 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1608, d24344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1608, d24344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1609 q = 1) (hb : d208033 q = 1) : d24345 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1609, d24345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1609, d24345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro56204 (p : Pattern) (ha : d1613 p = 1) (hb : d208033 p = 1) : d24349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1603 q = 1) (hb : d208033 q = 1) : d24339 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d24339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56201 q ha hb
    | true =>
      simp only [d1603, d24339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56202 q ha hb
  have h2 (q : Pattern) (ha : d1604 q = 1) (hb : d208033 q = 1) : d24340 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d24340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d24340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1605 q = 1) (hb : d208033 q = 1) : d24341 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d24341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d24341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1607 q = 1) (hb : d208033 q = 1) : d24343 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, d24343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1607, d24343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1612 q = 1) (hb : d208033 q = 1) : d24348 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1612, d24348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1612, d24348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1613 q = 1) (hb : d208033 q = 1) : d24349 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1613, d24349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1613, d24349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56205 (p : Pattern) (ha : d1619 p = 1) (hb : d208033 p = 1) : d24355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d208033 q = 1) : d24346 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d24346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56203 q ha hb
    | true =>
      simp only [d1610, d24346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d208033 q = 1) : d24347 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d24347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d24347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d208033 q = 1) : d24350 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56204 q ha hb
    | true =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d208033 q = 1) : d24351 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d208033 q = 1) : d24352 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d24352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d24352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d208033 q = 1) : d24353 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d24353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1617, d24353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1618 q = 1) (hb : d208033 q = 1) : d24354 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1618, d24354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1618, d24354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1619 q = 1) (hb : d208033 q = 1) : d24355 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1619, d24355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1619, d24355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56206 (p : Pattern) (ha : d1623 p = 1) (hb : d208033 p = 1) : d24359 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d208033 q = 1) : d24350 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56204 q ha hb
    | true =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d208033 q = 1) : d24351 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d208033 q = 1) : d24356 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d24356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d24356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d208033 q = 1) : d24357 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d24357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d24357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1622 q = 1) (hb : d208033 q = 1) : d24358 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, d24358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1622, d24358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1623 q = 1) (hb : d208033 q = 1) : d24359 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1623, d24359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1623, d24359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56207 (p : Pattern) (ha : d1629 p = 1) (hb : d208033 p = 1) : d24365 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1624 q = 1) (hb : d208033 q = 1) : d24360 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d24360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56205 q ha hb
    | true =>
      simp only [d1624, d24360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56206 q ha hb
  have h2 (q : Pattern) (ha : d1625 q = 1) (hb : d208033 q = 1) : d24361 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d24361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d24361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1626 q = 1) (hb : d208033 q = 1) : d24362 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d24362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1626, d24362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1627 q = 1) (hb : d208033 q = 1) : d24363 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d24363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d24363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1628 q = 1) (hb : d208033 q = 1) : d24364 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d24364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d24364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1629 q = 1) (hb : d208033 q = 1) : d24365 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1629, d24365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1629, d24365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56208 (p : Pattern) (ha : d1632 p = 1) (hb : d208033 p = 1) : d24368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d208033 q = 1) : d24346 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d24346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56203 q ha hb
    | true =>
      simp only [d1610, d24346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d208033 q = 1) : d24347 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d24347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d24347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d208033 q = 1) : d24350 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56204 q ha hb
    | true =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d208033 q = 1) : d24351 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d208033 q = 1) : d24352 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d24352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d24352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d208033 q = 1) : d24353 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d24353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1617, d24353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1618 q = 1) (hb : d208033 q = 1) : d24354 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1618, d24354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1618, d24354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1632 q = 1) (hb : d208033 q = 1) : d24368 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1632, d24368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1632, d24368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56209 (p : Pattern) (ha : d1633 p = 1) (hb : d208033 p = 1) : d24369 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d208033 q = 1) : d24350 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56204 q ha hb
    | true =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d208033 q = 1) : d24351 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d208033 q = 1) : d24356 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d24356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d24356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d208033 q = 1) : d24357 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d24357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d24357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1622 q = 1) (hb : d208033 q = 1) : d24358 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, d24358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1622, d24358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1633 q = 1) (hb : d208033 q = 1) : d24369 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1633, d24369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1633, d24369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56210 (p : Pattern) (ha : d1639 p = 1) (hb : d208033 p = 1) : d24375 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1624 q = 1) (hb : d208033 q = 1) : d24360 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d24360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56205 q ha hb
    | true =>
      simp only [d1624, d24360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56206 q ha hb
  have h2 (q : Pattern) (ha : d1625 q = 1) (hb : d208033 q = 1) : d24361 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d24361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d24361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1626 q = 1) (hb : d208033 q = 1) : d24362 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d24362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1626, d24362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1627 q = 1) (hb : d208033 q = 1) : d24363 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d24363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d24363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1628 q = 1) (hb : d208033 q = 1) : d24364 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d24364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d24364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1634 q = 1) (hb : d208033 q = 1) : d24370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d24370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56208 q ha hb
    | true =>
      simp only [d1634, d24370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56209 q ha hb
  have h7 (q : Pattern) (ha : d1635 q = 1) (hb : d208033 q = 1) : d24371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d24371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1635, d24371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1636 q = 1) (hb : d208033 q = 1) : d24372 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d24372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1636, d24372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1637 q = 1) (hb : d208033 q = 1) : d24373 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d24373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, d24373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1638 q = 1) (hb : d208033 q = 1) : d24374 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d24374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, d24374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1639 q = 1) (hb : d208033 q = 1) : d24375 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1639, d24375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1639, d24375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56211 (p : Pattern) (ha : d1832 p = 1) (hb : d208033 p = 1) : d24522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1624 q = 1) (hb : d208033 q = 1) : d24360 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d24360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56205 q ha hb
    | true =>
      simp only [d1624, d24360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56206 q ha hb
  have h2 (q : Pattern) (ha : d1625 q = 1) (hb : d208033 q = 1) : d24361 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d24361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d24361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1626 q = 1) (hb : d208033 q = 1) : d24362 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d24362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1626, d24362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1627 q = 1) (hb : d208033 q = 1) : d24363 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d24363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d24363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1628 q = 1) (hb : d208033 q = 1) : d24364 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d24364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d24364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1827 q = 1) (hb : d208033 q = 1) : d24517 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d24517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56206 q ha hb
    | true =>
      simp only [d1827, d24517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1828 q = 1) (hb : d208033 q = 1) : d24518 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d24518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d24518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1829 q = 1) (hb : d208033 q = 1) : d24519 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d24519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1829, d24519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1830 q = 1) (hb : d208033 q = 1) : d24520 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d24520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d24520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1831 q = 1) (hb : d208033 q = 1) : d24521 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d24521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d24521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1832 q = 1) (hb : d208033 q = 1) : d24522 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1832, d24522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1832, d24522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56212 (p : Pattern) (ha : d1838 p = 1) (hb : d208033 p = 1) : d24528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1827 q = 1) (hb : d208033 q = 1) : d24517 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d24517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56206 q ha hb
    | true =>
      simp only [d1827, d24517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1828 q = 1) (hb : d208033 q = 1) : d24518 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d24518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d24518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1829 q = 1) (hb : d208033 q = 1) : d24519 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d24519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1829, d24519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1830 q = 1) (hb : d208033 q = 1) : d24520 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d24520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d24520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1831 q = 1) (hb : d208033 q = 1) : d24521 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d24521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d24521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1833 q = 1) (hb : d208033 q = 1) : d24523 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, d24523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56209 q ha hb
    | true =>
      simp only [d1833, d24523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1834 q = 1) (hb : d208033 q = 1) : d24524 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d24524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, d24524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1835 q = 1) (hb : d208033 q = 1) : d24525 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d24525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1835, d24525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1836 q = 1) (hb : d208033 q = 1) : d24526 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, d24526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, d24526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1837 q = 1) (hb : d208033 q = 1) : d24527 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, d24527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, d24527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1838 q = 1) (hb : d208033 q = 1) : d24528 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1838, d24528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1838, d24528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56213 (p : Pattern) (ha : d1847 p = 1) (hb : d208033 p = 1) : d24537 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1833 q = 1) (hb : d208033 q = 1) : d24523 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, d24523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56209 q ha hb
    | true =>
      simp only [d1833, d24523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1834 q = 1) (hb : d208033 q = 1) : d24524 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d24524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, d24524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1835 q = 1) (hb : d208033 q = 1) : d24525 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d24525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1835, d24525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1836 q = 1) (hb : d208033 q = 1) : d24526 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, d24526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, d24526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1837 q = 1) (hb : d208033 q = 1) : d24527 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, d24527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, d24527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1847 q = 1) (hb : d208033 q = 1) : d24537 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1847, d24537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1847, d24537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56214 (p : Pattern) (ha : d1878 p = 1) (hb : d208033 p = 1) : d24568 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1862 q = 1) (hb : d208033 q = 1) : d24552 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d24552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d24552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56198 q ha hb
  have h2 (q : Pattern) (ha : d1570 q = 1) (hb : d208033 q = 1) : d24319 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d24319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56198 q ha hb
    | true =>
      simp only [d1570, d24319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1863 q = 1) (hb : d208033 q = 1) : d24553 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d24553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1863, d24553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1571 q = 1) (hb : d208033 q = 1) : d24320 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d24320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1571, d24320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1864 q = 1) (hb : d208033 q = 1) : d24554 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d24554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1864, d24554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1865 q = 1) (hb : d208033 q = 1) : d24555 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d24555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1865, d24555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1868 q = 1) (hb : d208033 q = 1) : d24558 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d24558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d24558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56199 q ha hb
  have h8 (q : Pattern) (ha : d1582 q = 1) (hb : d208033 q = 1) : d24327 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d24327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56199 q ha hb
    | true =>
      simp only [d1582, d24327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1869 q = 1) (hb : d208033 q = 1) : d24559 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d24559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1869, d24559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1583 q = 1) (hb : d208033 q = 1) : d24328 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d24328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1583, d24328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1870 q = 1) (hb : d208033 q = 1) : d24560 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d24560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1870, d24560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1871 q = 1) (hb : d208033 q = 1) : d24561 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d24561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1871, d24561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1872 q = 1) (hb : d208033 q = 1) : d24562 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1872, d24562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1872, d24562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1877 q = 1) (hb : d208033 q = 1) : d24567 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d24567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1877, d24567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d1878 q = 1) (hb : d208033 q = 1) : d24568 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1878, d24568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1878, d24568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56215 (p : Pattern) (ha : d1888 p = 1) (hb : d208033 p = 1) : d24573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1868 q = 1) (hb : d208033 q = 1) : d24558 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d24558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d24558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56199 q ha hb
  have h2 (q : Pattern) (ha : d1582 q = 1) (hb : d208033 q = 1) : d24327 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d24327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56199 q ha hb
    | true =>
      simp only [d1582, d24327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1869 q = 1) (hb : d208033 q = 1) : d24559 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d24559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1869, d24559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1583 q = 1) (hb : d208033 q = 1) : d24328 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d24328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1583, d24328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1870 q = 1) (hb : d208033 q = 1) : d24560 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d24560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1870, d24560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1871 q = 1) (hb : d208033 q = 1) : d24561 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d24561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1871, d24561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1877 q = 1) (hb : d208033 q = 1) : d24567 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d24567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1877, d24567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1887 q = 1) (hb : d208033 q = 1) : d1887 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1888 q = 1) (hb : d208033 q = 1) : d24573 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1888, d24573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1888, d24573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro56216 (p : Pattern) (ha : d1907 p = 1) (hb : d208033 p = 1) : d24592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1889 q = 1) (hb : d208033 q = 1) : d24574 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d24574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56214 q ha hb
    | true =>
      simp only [d1889, d24574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56215 q ha hb
  have h2 (q : Pattern) (ha : d1890 q = 1) (hb : d208033 q = 1) : d24575 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d24575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d24575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1891 q = 1) (hb : d208033 q = 1) : d24576 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d24576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d24576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1897 q = 1) (hb : d208033 q = 1) : d24582 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d24582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1897, d24582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1906 q = 1) (hb : d208033 q = 1) : d24591 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1906, d24591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1906, d24591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1907 q = 1) (hb : d208033 q = 1) : d24592 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1907, d24592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1907, d24592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56217 (p : Pattern) (ha : d1974 p = 1) (hb : d208033 p = 1) : d24667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1908 q = 1) (hb : d208033 q = 1) : d24593 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d24593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56216 q ha hb
    | true =>
      simp only [d1908, d24593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1909 q = 1) (hb : d208033 q = 1) : d24594 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d24594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d24594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1971 q = 1) (hb : d208033 q = 1) : d24664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1971, d24664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1971, d24664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1972 q = 1) (hb : d208033 q = 1) : d24665 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1972, d24665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1972, d24665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1973 q = 1) (hb : d208033 q = 1) : d24666 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1973, d24666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1973, d24666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1974 q = 1) (hb : d208033 q = 1) : d24667 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1974, d24667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1974, d24667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56218 (p : Pattern) (ha : d1980 p = 1) (hb : d208033 p = 1) : d24673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1975 q = 1) (hb : d208033 q = 1) : d24668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1975, d24668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56217 q ha hb
    | true =>
      simp only [d1975, d24668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1976 q = 1) (hb : d208033 q = 1) : d24669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1976, d24669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1976, d24669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1977 q = 1) (hb : d208033 q = 1) : d24670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1977, d24670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1977, d24670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1978 q = 1) (hb : d208033 q = 1) : d24671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1978, d24671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1978, d24671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1979 q = 1) (hb : d208033 q = 1) : d24672 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1979, d24672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1979, d24672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1980 q = 1) (hb : d208033 q = 1) : d24673 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1980, d24673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1980, d24673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56219 (p : Pattern) (ha : d1644 p = 1) (hb : d208033 p = 1) : d24380 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d208033 q = 1) : d24346 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d24346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56203 q ha hb
    | true =>
      simp only [d1610, d24346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d208033 q = 1) : d24347 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d24347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d24347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d208033 q = 1) : d24350 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56204 q ha hb
    | true =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d208033 q = 1) : d24351 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d208033 q = 1) : d24352 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d24352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d24352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d208033 q = 1) : d24353 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d24353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1617, d24353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1643 q = 1) (hb : d208033 q = 1) : d24379 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1643, d24379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1643, d24379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1644 q = 1) (hb : d208033 q = 1) : d24380 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1644, d24380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1644, d24380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56220 (p : Pattern) (ha : d1646 p = 1) (hb : d208033 p = 1) : d24382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d208033 q = 1) : d24350 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56204 q ha hb
    | true =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d208033 q = 1) : d24351 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d208033 q = 1) : d24356 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d24356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d24356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d208033 q = 1) : d24357 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d24357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d24357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1645 q = 1) (hb : d208033 q = 1) : d24381 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d24381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, d24381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1646 q = 1) (hb : d208033 q = 1) : d24382 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1646, d24382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1646, d24382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56221 (p : Pattern) (ha : d1653 p = 1) (hb : d208033 p = 1) : d24389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d208033 q = 1) : d24346 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d24346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56203 q ha hb
    | true =>
      simp only [d1610, d24346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d208033 q = 1) : d24347 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d24347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d24347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d208033 q = 1) : d24350 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56204 q ha hb
    | true =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d208033 q = 1) : d24351 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d208033 q = 1) : d24352 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d24352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d24352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1651 q = 1) (hb : d208033 q = 1) : d24387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1651, d24387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1651, d24387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1652 q = 1) (hb : d208033 q = 1) : d24388 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1652, d24388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1652, d24388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1653 q = 1) (hb : d208033 q = 1) : d24389 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1653, d24389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1653, d24389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56222 (p : Pattern) (ha : d1656 p = 1) (hb : d208033 p = 1) : d24392 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d208033 q = 1) : d24350 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56204 q ha hb
    | true =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d208033 q = 1) : d24351 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d208033 q = 1) : d24356 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d24356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d24356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1654 q = 1) (hb : d208033 q = 1) : d24390 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d24390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, d24390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1655 q = 1) (hb : d208033 q = 1) : d24391 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, d24391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1655, d24391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d208033 q = 1) : d24392 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1656, d24392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1656, d24392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56223 (p : Pattern) (ha : d1664 p = 1) (hb : d208033 p = 1) : d24398 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1660 q = 1) : d1660 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1661 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1662 q = 1) (hb : d208033 q = 1) : d24396 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1662, d208033, d24396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1662, d208033, d24396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1663 q = 1) (hb : d208033 q = 1) : d24397 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1663, d24397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1663, d24397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d1530 q = 1) : d1530 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1536 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1537 q = 1) (hb : d208033 q = 1) : d24307 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1537, d208033, d24307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1537, d208033, d24307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1538 q = 1) (hb : d208033 q = 1) : d24308 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1538, d24308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1538, d24308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d1664 q = 1) (hb : d208033 q = 1) : d24398 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1664, d24398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1664, d24398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro56224 (p : Pattern) (ha : d1670 p = 1) (hb : d208033 p = 1) : d24404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1665 q = 1) (hb : d208033 q = 1) : d24399 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d24399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56223 q ha hb
    | true =>
      simp only [d1665, d24399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1666 q = 1) (hb : d208033 q = 1) : d24400 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d24400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1666, d24400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1667 q = 1) (hb : d208033 q = 1) : d24401 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1667, d24401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1667, d24401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1668 q = 1) (hb : d208033 q = 1) : d24402 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1668, d24402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1668, d24402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1555 q = 1) (hb : d208033 q = 1) : d24312 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d24312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56197 q ha hb
    | true =>
      simp only [d1555, d24312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1556 q = 1) (hb : d208033 q = 1) : d24313 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d24313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1556, d24313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1557 q = 1) (hb : d208033 q = 1) : d24314 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d24314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1557, d24314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1558 q = 1) (hb : d208033 q = 1) : d24315 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d24315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1558, d24315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1669 q = 1) (hb : d208033 q = 1) : d24403 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1669, d24403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1669, d24403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1570 q = 1) (hb : d208033 q = 1) : d24319 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d24319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56198 q ha hb
    | true =>
      simp only [d1570, d24319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1571 q = 1) (hb : d208033 q = 1) : d24320 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d24320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1571, d24320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1572 q = 1) (hb : d208033 q = 1) : d24321 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d24321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d24321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1573 q = 1) (hb : d208033 q = 1) : d24322 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d24322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1573, d24322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d1574 q = 1) (hb : d208033 q = 1) : d24323 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1574, d24323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1574, d24323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1670 q = 1) (hb : d208033 q = 1) : d24404 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1670, d24404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1670, d24404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56225 (p : Pattern) (ha : d1676 p = 1) (hb : d208033 p = 1) : d24410 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1671 q = 1) (hb : d208033 q = 1) : d24405 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1671, d24405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56224 q ha hb
    | true =>
      simp only [d1671, d24405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56200 q ha hb
  have h2 (q : Pattern) (ha : d1672 q = 1) (hb : d208033 q = 1) : d24406 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1672, d24406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1672, d24406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1673 q = 1) (hb : d208033 q = 1) : d24407 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1673, d24407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1673, d24407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1590 q = 1) (hb : d208033 q = 1) : d24335 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d24335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56200 q ha hb
    | true =>
      simp only [d1590, d24335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56201 q ha hb
  have h5 (q : Pattern) (ha : d1591 q = 1) (hb : d208033 q = 1) : d24336 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d24336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d24336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1592 q = 1) (hb : d208033 q = 1) : d24337 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d24337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d24337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1674 q = 1) (hb : d208033 q = 1) : d24408 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1674, d24408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1674, d24408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1603 q = 1) (hb : d208033 q = 1) : d24339 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d24339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56201 q ha hb
    | true =>
      simp only [d1603, d24339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56202 q ha hb
  have h9 (q : Pattern) (ha : d1604 q = 1) (hb : d208033 q = 1) : d24340 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d24340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d24340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1605 q = 1) (hb : d208033 q = 1) : d24341 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d24341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d24341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1606 q = 1) (hb : d208033 q = 1) : d24342 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, d24342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1606, d24342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1675 q = 1) (hb : d208033 q = 1) : d24409 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1675, d24409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1675, d24409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1676 q = 1) (hb : d208033 q = 1) : d24410 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1676, d24410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1676, d24410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro56226 (p : Pattern) (ha : d1682 p = 1) (hb : d208033 p = 1) : d24416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1677 q = 1) (hb : d208033 q = 1) : d24411 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, d24411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56225 q ha hb
    | true =>
      simp only [d1677, d24411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1678 q = 1) (hb : d208033 q = 1) : d24412 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1678, d24412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1678, d24412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1610 q = 1) (hb : d208033 q = 1) : d24346 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d24346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56203 q ha hb
    | true =>
      simp only [d1610, d24346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1611 q = 1) (hb : d208033 q = 1) : d24347 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d24347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d24347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1679 q = 1) (hb : d208033 q = 1) : d24413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1679, d24413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1679, d24413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1680 q = 1) (hb : d208033 q = 1) : d24414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1680, d24414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1680, d24414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1681 q = 1) (hb : d208033 q = 1) : d24415 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1681, d24415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1681, d24415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1682 q = 1) (hb : d208033 q = 1) : d24416 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1682, d24416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1682, d24416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56227 (p : Pattern) (ha : d5635 p = 1) (hb : d208033 p = 1) : d24473 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1570 q = 1) (hb : d208033 q = 1) : d24319 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d24319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56198 q ha hb
    | true =>
      simp only [d1570, d24319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1571 q = 1) (hb : d208033 q = 1) : d24320 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d24320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1571, d24320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1572 q = 1) (hb : d208033 q = 1) : d24321 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d24321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d24321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1573 q = 1) (hb : d208033 q = 1) : d24322 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d24322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1573, d24322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1582 q = 1) (hb : d208033 q = 1) : d24327 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d24327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56199 q ha hb
    | true =>
      simp only [d1582, d24327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1583 q = 1) (hb : d208033 q = 1) : d24328 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d24328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1583, d24328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1584 q = 1) (hb : d208033 q = 1) : d24329 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d24329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d24329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1585 q = 1) (hb : d208033 q = 1) : d24330 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d24330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1585, d24330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1586 q = 1) (hb : d208033 q = 1) : d24331 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1586, d24331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1586, d24331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5634 q = 1) (hb : d208033 q = 1) : d5634 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5635 q = 1) (hb : d208033 q = 1) : d24473 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5635, d24473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5635, d24473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro56228 (p : Pattern) (ha : d5642 p = 1) (hb : d208033 p = 1) : d24479 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1590 q = 1) (hb : d208033 q = 1) : d24335 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d24335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56200 q ha hb
    | true =>
      simp only [d1590, d24335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56201 q ha hb
  have h2 (q : Pattern) (ha : d1591 q = 1) (hb : d208033 q = 1) : d24336 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d24336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d24336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1592 q = 1) (hb : d208033 q = 1) : d24337 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d24337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d24337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1603 q = 1) (hb : d208033 q = 1) : d24339 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d24339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56201 q ha hb
    | true =>
      simp only [d1603, d24339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56202 q ha hb
  have h5 (q : Pattern) (ha : d1604 q = 1) (hb : d208033 q = 1) : d24340 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d24340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d24340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1605 q = 1) (hb : d208033 q = 1) : d24341 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d24341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d24341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1606 q = 1) (hb : d208033 q = 1) : d24342 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, d24342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1606, d24342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5636 q = 1) (hb : d208033 q = 1) : d5636 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d5637 q = 1) (hb : d208033 q = 1) : d24474 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5637, d24474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56227 q ha hb
    | true =>
      simp only [d5637, d24474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5638 q = 1) (hb : d208033 q = 1) : d24475 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5638, d24475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5638, d24475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5639 q = 1) (hb : d208033 q = 1) : d24476 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5639, d24476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5639, d24476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5640 q = 1) (hb : d208033 q = 1) : d24477 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5640, d24477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5640, d24477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5641 q = 1) (hb : d208033 q = 1) : d24478 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5641, d24478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5641, d24478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5642 q = 1) (hb : d208033 q = 1) : d24479 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5642, d24479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5642, d24479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro56229 (p : Pattern) (ha : d5648 p = 1) (hb : d208033 p = 1) : d24485 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5643 q = 1) (hb : d208033 q = 1) : d24480 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5643, d24480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56228 q ha hb
    | true =>
      simp only [d5643, d24480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5644 q = 1) (hb : d208033 q = 1) : d24481 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5644, d24481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5644, d24481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5645 q = 1) (hb : d208033 q = 1) : d24482 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5645, d24482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5645, d24482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5646 q = 1) (hb : d208033 q = 1) : d24483 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5646, d24483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5646, d24483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5647 q = 1) (hb : d208033 q = 1) : d24484 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5647, d24484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5647, d24484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5648 q = 1) (hb : d208033 q = 1) : d24485 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5648, d24485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5648, d24485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro56230 (p : Pattern) (ha : d74729 p = 1) (hb : d208033 p = 1) : d211286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1647 q = 1) (hb : d208033 q = 1) : d24383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d24383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56219 q ha hb
    | true =>
      simp only [d1647, d24383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56220 q ha hb
  have h2 (q : Pattern) (ha : d1648 q = 1) (hb : d208033 q = 1) : d24384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d24384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, d24384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1649 q = 1) (hb : d208033 q = 1) : d24385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d24385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1649, d24385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1650 q = 1) (hb : d208033 q = 1) : d24386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d24386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d24386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1657 q = 1) (hb : d208033 q = 1) : d24393 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d24393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56221 q ha hb
    | true =>
      simp only [d1657, d24393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56222 q ha hb
  have h6 (q : Pattern) (ha : d1658 q = 1) (hb : d208033 q = 1) : d24394 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d24394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d24394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1659 q = 1) (hb : d208033 q = 1) : d24395 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d24395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1659, d24395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1683 q = 1) (hb : d208033 q = 1) : d24417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d24417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56226 q ha hb
    | true =>
      simp only [d1683, d24417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56205 q ha hb
  have h9 (q : Pattern) (ha : d4525 q = 1) (hb : d208033 q = 1) : d211282 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d211282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4525, d211282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5649 q = 1) (hb : d208033 q = 1) : d24486 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5649, d24486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56229 q ha hb
    | true =>
      simp only [d5649, d24486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5650 q = 1) (hb : d208033 q = 1) : d24487 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5650, d24487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5650, d24487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74726 q = 1) (hb : d208033 q = 1) : d211283 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74726, d211283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74726, d211283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74727 q = 1) (hb : d208033 q = 1) : d211284 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74727, d211284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74727, d211284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74728 q = 1) (hb : d208033 q = 1) : d211285 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74728, d211285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74728, d211285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74729 q = 1) (hb : d208033 q = 1) : d211286 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74729, d211286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74729, d211286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56231 (p : Pattern) (ha : d1803 p = 1) (hb : d208033 p = 1) : d24492 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d208033 q = 1) : d24346 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d24346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56203 q ha hb
    | true =>
      simp only [d1610, d24346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d208033 q = 1) : d24347 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d24347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d24347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d208033 q = 1) : d24350 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56204 q ha hb
    | true =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d208033 q = 1) : d24351 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d208033 q = 1) : d24352 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d24352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d24352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d208033 q = 1) : d24353 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d24353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1617, d24353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1643 q = 1) (hb : d208033 q = 1) : d24379 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1643, d24379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1643, d24379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1803 q = 1) (hb : d208033 q = 1) : d24492 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1803, d24492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1803, d24492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56232 (p : Pattern) (ha : d1804 p = 1) (hb : d208033 p = 1) : d24493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d208033 q = 1) : d24350 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56204 q ha hb
    | true =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d208033 q = 1) : d24351 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d208033 q = 1) : d24356 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d24356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d24356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d208033 q = 1) : d24357 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d24357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d24357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1645 q = 1) (hb : d208033 q = 1) : d24381 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d24381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, d24381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1804 q = 1) (hb : d208033 q = 1) : d24493 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1804, d24493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1804, d24493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56233 (p : Pattern) (ha : d1809 p = 1) (hb : d208033 p = 1) : d24498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d208033 q = 1) : d24346 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d24346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56203 q ha hb
    | true =>
      simp only [d1610, d24346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d208033 q = 1) : d24347 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d24347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d24347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d208033 q = 1) : d24350 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56204 q ha hb
    | true =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d208033 q = 1) : d24351 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d208033 q = 1) : d24352 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d24352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d24352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1651 q = 1) (hb : d208033 q = 1) : d24387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1651, d24387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1651, d24387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1652 q = 1) (hb : d208033 q = 1) : d24388 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1652, d24388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1652, d24388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1809 q = 1) (hb : d208033 q = 1) : d24498 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1809, d24498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1809, d24498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56234 (p : Pattern) (ha : d1810 p = 1) (hb : d208033 p = 1) : d24499 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d208033 q = 1) : d24350 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56204 q ha hb
    | true =>
      simp only [d1614, d24350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d208033 q = 1) : d24351 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d24351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d208033 q = 1) : d24356 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d24356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d24356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1654 q = 1) (hb : d208033 q = 1) : d24390 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d24390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, d24390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1655 q = 1) (hb : d208033 q = 1) : d24391 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, d24391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1655, d24391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1810 q = 1) (hb : d208033 q = 1) : d24499 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1810, d24499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1810, d24499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56235 (p : Pattern) (ha : d1814 p = 1) (hb : d208033 p = 1) : d24503 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1677 q = 1) (hb : d208033 q = 1) : d24411 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, d24411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56225 q ha hb
    | true =>
      simp only [d1677, d24411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1678 q = 1) (hb : d208033 q = 1) : d24412 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1678, d24412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1678, d24412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1610 q = 1) (hb : d208033 q = 1) : d24346 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d24346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56203 q ha hb
    | true =>
      simp only [d1610, d24346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1611 q = 1) (hb : d208033 q = 1) : d24347 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d24347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d24347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1679 q = 1) (hb : d208033 q = 1) : d24413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1679, d24413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1679, d24413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1680 q = 1) (hb : d208033 q = 1) : d24414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1680, d24414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1680, d24414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1681 q = 1) (hb : d208033 q = 1) : d24415 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1681, d24415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1681, d24415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1814 q = 1) (hb : d208033 q = 1) : d24503 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1814, d24503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1814, d24503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56236 (p : Pattern) (ha : d5655 p = 1) (hb : d208033 p = 1) : d24509 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5643 q = 1) (hb : d208033 q = 1) : d24480 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5643, d24480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56228 q ha hb
    | true =>
      simp only [d5643, d24480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5644 q = 1) (hb : d208033 q = 1) : d24481 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5644, d24481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5644, d24481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5645 q = 1) (hb : d208033 q = 1) : d24482 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5645, d24482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5645, d24482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5646 q = 1) (hb : d208033 q = 1) : d24483 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5646, d24483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5646, d24483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5647 q = 1) (hb : d208033 q = 1) : d24484 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5647, d24484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5647, d24484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5655 q = 1) (hb : d208033 q = 1) : d24509 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5655, d24509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5655, d24509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56237 (p : Pattern) (ha : d74733 p = 1) (hb : d208033 p = 1) : d211291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1647 q = 1) (hb : d208033 q = 1) : d24383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d24383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56219 q ha hb
    | true =>
      simp only [d1647, d24383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56220 q ha hb
  have h2 (q : Pattern) (ha : d1648 q = 1) (hb : d208033 q = 1) : d24384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d24384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, d24384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1649 q = 1) (hb : d208033 q = 1) : d24385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d24385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1649, d24385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1650 q = 1) (hb : d208033 q = 1) : d24386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d24386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d24386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1657 q = 1) (hb : d208033 q = 1) : d24393 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d24393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56221 q ha hb
    | true =>
      simp only [d1657, d24393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56222 q ha hb
  have h6 (q : Pattern) (ha : d1658 q = 1) (hb : d208033 q = 1) : d24394 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d24394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d24394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1659 q = 1) (hb : d208033 q = 1) : d24395 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d24395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1659, d24395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1683 q = 1) (hb : d208033 q = 1) : d24417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d24417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56226 q ha hb
    | true =>
      simp only [d1683, d24417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56205 q ha hb
  have h9 (q : Pattern) (ha : d4525 q = 1) (hb : d208033 q = 1) : d211282 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d211282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4525, d211282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5649 q = 1) (hb : d208033 q = 1) : d24486 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5649, d24486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56229 q ha hb
    | true =>
      simp only [d5649, d24486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5650 q = 1) (hb : d208033 q = 1) : d24487 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5650, d24487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5650, d24487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74726 q = 1) (hb : d208033 q = 1) : d211283 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74726, d211283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74726, d211283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74727 q = 1) (hb : d208033 q = 1) : d211284 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74727, d211284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74727, d211284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74728 q = 1) (hb : d208033 q = 1) : d211285 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74728, d211285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74728, d211285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1805 q = 1) (hb : d208033 q = 1) : d24494 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1805, d24494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56231 q ha hb
    | true =>
      simp only [d1805, d24494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56232 q ha hb
  have h16 (q : Pattern) (ha : d1806 q = 1) (hb : d208033 q = 1) : d24495 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1806, d24495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1806, d24495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1807 q = 1) (hb : d208033 q = 1) : d24496 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1807, d24496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1807, d24496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d1808 q = 1) (hb : d208033 q = 1) : d24497 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1808, d24497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1808, d24497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1811 q = 1) (hb : d208033 q = 1) : d24500 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1811, d24500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56233 q ha hb
    | true =>
      simp only [d1811, d24500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56234 q ha hb
  have h20 (q : Pattern) (ha : d1812 q = 1) (hb : d208033 q = 1) : d24501 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1812, d24501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1812, d24501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d1813 q = 1) (hb : d208033 q = 1) : d24502 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1813, d24502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d1813, d24502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d1815 q = 1) (hb : d208033 q = 1) : d24504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d24504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56235 q ha hb
    | true =>
      simp only [d1815, d24504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56208 q ha hb
  have h23 (q : Pattern) (ha : d4530 q = 1) (hb : d208033 q = 1) : d211287 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d211287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4530, d211287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d5656 q = 1) (hb : d208033 q = 1) : d24510 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5656, d24510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56236 q ha hb
    | true =>
      simp only [d5656, d24510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d5657 q = 1) (hb : d208033 q = 1) : d24511 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5657, d24511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5657, d24511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d74730 q = 1) (hb : d208033 q = 1) : d211288 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74730, d211288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d74730, d211288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d74731 q = 1) (hb : d208033 q = 1) : d211289 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74731, d211289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74731, d211289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d74732 q = 1) (hb : d208033 q = 1) : d211290 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74732, d211290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74732, d211290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d74733 q = 1) (hb : d208033 q = 1) : d211291 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74733, d211291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74733, d211291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro56238 (p : Pattern) (ha : d74740 p = 1) (hb : d208033 p = 1) : d211298 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1815 q = 1) (hb : d208033 q = 1) : d24504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d24504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56235 q ha hb
    | true =>
      simp only [d1815, d24504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56208 q ha hb
  have h2 (q : Pattern) (ha : d4530 q = 1) (hb : d208033 q = 1) : d211287 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d211287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4530, d211287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5656 q = 1) (hb : d208033 q = 1) : d24510 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5656, d24510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56236 q ha hb
    | true =>
      simp only [d5656, d24510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5657 q = 1) (hb : d208033 q = 1) : d24511 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5657, d24511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5657, d24511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74730 q = 1) (hb : d208033 q = 1) : d211288 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74730, d211288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74730, d211288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74738 q = 1) (hb : d208033 q = 1) : d211296 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74738, d211296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74738, d211296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74739 q = 1) (hb : d208033 q = 1) : d211297 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74739, d211297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74739, d211297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74740 q = 1) (hb : d208033 q = 1) : d211298 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74740, d211298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74740, d211298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56239 (p : Pattern) (ha : d1867 p = 1) (hb : d208033 p = 1) : d24557 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1853 q = 1) (hb : d208033 q = 1) : d24543 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1853, d24543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1853, d24543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56223 q ha hb
  have h2 (q : Pattern) (ha : d1665 q = 1) (hb : d208033 q = 1) : d24399 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d24399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56223 q ha hb
    | true =>
      simp only [d1665, d24399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1854 q = 1) (hb : d208033 q = 1) : d24544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1854, d24544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1854, d24544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1666 q = 1) (hb : d208033 q = 1) : d24400 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d24400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1666, d24400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1855 q = 1) (hb : d208033 q = 1) : d24545 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1855, d24545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1855, d24545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1856 q = 1) (hb : d208033 q = 1) : d24546 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1856, d24546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1856, d24546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1857 q = 1) (hb : d208033 q = 1) : d24547 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, d24547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1857, d24547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56197 q ha hb
  have h8 (q : Pattern) (ha : d1555 q = 1) (hb : d208033 q = 1) : d24312 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d24312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56197 q ha hb
    | true =>
      simp only [d1555, d24312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1858 q = 1) (hb : d208033 q = 1) : d24548 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, d24548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1858, d24548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1556 q = 1) (hb : d208033 q = 1) : d24313 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d24313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1556, d24313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1859 q = 1) (hb : d208033 q = 1) : d24549 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, d24549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1859, d24549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1860 q = 1) (hb : d208033 q = 1) : d24550 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, d24550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1860, d24550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1861 q = 1) (hb : d208033 q = 1) : d24551 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1861, d24551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1861, d24551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1862 q = 1) (hb : d208033 q = 1) : d24552 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d24552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d24552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56198 q ha hb
  have h15 (q : Pattern) (ha : d1570 q = 1) (hb : d208033 q = 1) : d24319 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d24319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56198 q ha hb
    | true =>
      simp only [d1570, d24319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d1863 q = 1) (hb : d208033 q = 1) : d24553 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d24553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1863, d24553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1571 q = 1) (hb : d208033 q = 1) : d24320 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d24320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1571, d24320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d1864 q = 1) (hb : d208033 q = 1) : d24554 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d24554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1864, d24554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1865 q = 1) (hb : d208033 q = 1) : d24555 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d24555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d1865, d24555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d1866 q = 1) (hb : d208033 q = 1) : d24556 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1866, d24556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1866, d24556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d1867 q = 1) (hb : d208033 q = 1) : d24557 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1867, d24557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1867, d24557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro56240 (p : Pattern) (ha : d1873 p = 1) (hb : d208033 p = 1) : d24563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1857 q = 1) (hb : d208033 q = 1) : d24547 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, d24547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1857, d24547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56197 q ha hb
  have h2 (q : Pattern) (ha : d1555 q = 1) (hb : d208033 q = 1) : d24312 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d24312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56197 q ha hb
    | true =>
      simp only [d1555, d24312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1858 q = 1) (hb : d208033 q = 1) : d24548 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, d24548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1858, d24548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1556 q = 1) (hb : d208033 q = 1) : d24313 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d24313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1556, d24313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1859 q = 1) (hb : d208033 q = 1) : d24549 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, d24549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1859, d24549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1860 q = 1) (hb : d208033 q = 1) : d24550 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, d24550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1860, d24550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1862 q = 1) (hb : d208033 q = 1) : d24552 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d24552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d24552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56198 q ha hb
  have h8 (q : Pattern) (ha : d1570 q = 1) (hb : d208033 q = 1) : d24319 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d24319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56198 q ha hb
    | true =>
      simp only [d1570, d24319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1863 q = 1) (hb : d208033 q = 1) : d24553 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d24553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1863, d24553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1571 q = 1) (hb : d208033 q = 1) : d24320 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d24320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1571, d24320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1864 q = 1) (hb : d208033 q = 1) : d24554 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d24554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1864, d24554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1865 q = 1) (hb : d208033 q = 1) : d24555 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d24555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1865, d24555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1866 q = 1) (hb : d208033 q = 1) : d24556 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1866, d24556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1866, d24556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1868 q = 1) (hb : d208033 q = 1) : d24558 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d24558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d24558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56199 q ha hb
  have h15 (q : Pattern) (ha : d1582 q = 1) (hb : d208033 q = 1) : d24327 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d24327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56199 q ha hb
    | true =>
      simp only [d1582, d24327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d1869 q = 1) (hb : d208033 q = 1) : d24559 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d24559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1869, d24559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1583 q = 1) (hb : d208033 q = 1) : d24328 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d24328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1583, d24328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d1870 q = 1) (hb : d208033 q = 1) : d24560 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d24560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1870, d24560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1871 q = 1) (hb : d208033 q = 1) : d24561 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d24561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d1871, d24561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d1872 q = 1) (hb : d208033 q = 1) : d24562 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1872, d24562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1872, d24562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d1873 q = 1) (hb : d208033 q = 1) : d24563 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1873, d24563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1873, d24563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro56241 (p : Pattern) (ha : d1894 p = 1) (hb : d208033 p = 1) : d24579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1874 q = 1) (hb : d208033 q = 1) : d24564 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1874, d24564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56239 q ha hb
    | true =>
      simp only [d1874, d24564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56240 q ha hb
  have h2 (q : Pattern) (ha : d1875 q = 1) (hb : d208033 q = 1) : d24565 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1875, d24565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1875, d24565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1876 q = 1) (hb : d208033 q = 1) : d24566 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1876, d24566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1876, d24566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1879 q = 1) (hb : d208033 q = 1) : d24569 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d24569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56240 q ha hb
    | true =>
      simp only [d1879, d24569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56214 q ha hb
  have h5 (q : Pattern) (ha : d1880 q = 1) (hb : d208033 q = 1) : d24570 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d24570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d24570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1881 q = 1) (hb : d208033 q = 1) : d24571 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d24571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d24571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1882 q = 1) (hb : d208033 q = 1) : d24572 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1882, d24572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1882, d24572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1889 q = 1) (hb : d208033 q = 1) : d24574 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d24574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56214 q ha hb
    | true =>
      simp only [d1889, d24574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56215 q ha hb
  have h9 (q : Pattern) (ha : d1890 q = 1) (hb : d208033 q = 1) : d24575 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d24575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d24575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1891 q = 1) (hb : d208033 q = 1) : d24576 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d24576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d24576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1892 q = 1) (hb : d208033 q = 1) : d24577 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d24577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1892, d24577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1893 q = 1) (hb : d208033 q = 1) : d24578 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1893, d24578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1893, d24578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1894 q = 1) (hb : d208033 q = 1) : d24579 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1894, d24579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1894, d24579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro56242 (p : Pattern) (ha : d1899 p = 1) (hb : d208033 p = 1) : d24584 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1879 q = 1) (hb : d208033 q = 1) : d24569 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d24569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56240 q ha hb
    | true =>
      simp only [d1879, d24569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56214 q ha hb
  have h2 (q : Pattern) (ha : d1880 q = 1) (hb : d208033 q = 1) : d24570 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d24570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d24570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1881 q = 1) (hb : d208033 q = 1) : d24571 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d24571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d24571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1889 q = 1) (hb : d208033 q = 1) : d24574 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d24574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56214 q ha hb
    | true =>
      simp only [d1889, d24574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56215 q ha hb
  have h5 (q : Pattern) (ha : d1890 q = 1) (hb : d208033 q = 1) : d24575 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d24575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d24575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1891 q = 1) (hb : d208033 q = 1) : d24576 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d24576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d24576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1892 q = 1) (hb : d208033 q = 1) : d24577 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d24577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1892, d24577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1897 q = 1) (hb : d208033 q = 1) : d24582 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d24582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1897, d24582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1898 q = 1) (hb : d208033 q = 1) : d24583 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1898, d24583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1898, d24583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1899 q = 1) (hb : d208033 q = 1) : d24584 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1899, d24584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1899, d24584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro56243 (p : Pattern) (ha : d1905 p = 1) (hb : d208033 p = 1) : d24590 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1895 q = 1) (hb : d208033 q = 1) : d24580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1895, d24580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56241 q ha hb
    | true =>
      simp only [d1895, d24580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1896 q = 1) (hb : d208033 q = 1) : d24581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1896, d24581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1896, d24581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1900 q = 1) (hb : d208033 q = 1) : d24585 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1900, d24585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56242 q ha hb
    | true =>
      simp only [d1900, d24585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1901 q = 1) (hb : d208033 q = 1) : d24586 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1901, d24586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1901, d24586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1902 q = 1) (hb : d208033 q = 1) : d24587 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1902, d24587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1902, d24587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1903 q = 1) (hb : d208033 q = 1) : d24588 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1903, d24588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1903, d24588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1904 q = 1) (hb : d208033 q = 1) : d24589 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1904, d24589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1904, d24589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1905 q = 1) (hb : d208033 q = 1) : d24590 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1905, d24590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1905, d24590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56244 (p : Pattern) (ha : d1913 p = 1) (hb : d208033 p = 1) : d24598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1900 q = 1) (hb : d208033 q = 1) : d24585 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1900, d24585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56242 q ha hb
    | true =>
      simp only [d1900, d24585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1901 q = 1) (hb : d208033 q = 1) : d24586 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1901, d24586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1901, d24586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1908 q = 1) (hb : d208033 q = 1) : d24593 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d24593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56216 q ha hb
    | true =>
      simp only [d1908, d24593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d208033 q = 1) : d24594 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d24594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d24594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1910 q = 1) (hb : d208033 q = 1) : d24595 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1910, d24595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1910, d24595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1911 q = 1) (hb : d208033 q = 1) : d24596 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1911, d24596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1911, d24596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1912 q = 1) (hb : d208033 q = 1) : d24597 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1912, d24597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1912, d24597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1913 q = 1) (hb : d208033 q = 1) : d24598 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1913, d24598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1913, d24598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro56245 (p : Pattern) (ha : d5679 p = 1) (hb : d208033 p = 1) : d24644 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1862 q = 1) (hb : d208033 q = 1) : d24552 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d24552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d24552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56198 q ha hb
  have h2 (q : Pattern) (ha : d1570 q = 1) (hb : d208033 q = 1) : d24319 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d24319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56198 q ha hb
    | true =>
      simp only [d1570, d24319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1863 q = 1) (hb : d208033 q = 1) : d24553 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d24553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1863, d24553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1571 q = 1) (hb : d208033 q = 1) : d24320 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d24320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1571, d24320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1864 q = 1) (hb : d208033 q = 1) : d24554 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d24554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1864, d24554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1865 q = 1) (hb : d208033 q = 1) : d24555 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d24555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1865, d24555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1868 q = 1) (hb : d208033 q = 1) : d24558 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d24558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d24558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56199 q ha hb
  have h8 (q : Pattern) (ha : d1582 q = 1) (hb : d208033 q = 1) : d24327 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d24327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56199 q ha hb
    | true =>
      simp only [d1582, d24327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1869 q = 1) (hb : d208033 q = 1) : d24559 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d24559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1869, d24559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1583 q = 1) (hb : d208033 q = 1) : d24328 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d24328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1583, d24328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1870 q = 1) (hb : d208033 q = 1) : d24560 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d24560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1870, d24560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1871 q = 1) (hb : d208033 q = 1) : d24561 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d24561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1871, d24561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1872 q = 1) (hb : d208033 q = 1) : d24562 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1872, d24562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1872, d24562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5678 q = 1) (hb : d208033 q = 1) : d5678 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d5679 q = 1) (hb : d208033 q = 1) : d24644 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5679, d24644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5679, d24644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro56246 (p : Pattern) (ha : d5686 p = 1) (hb : d208033 p = 1) : d24650 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1879 q = 1) (hb : d208033 q = 1) : d24569 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d24569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56240 q ha hb
    | true =>
      simp only [d1879, d24569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56214 q ha hb
  have h2 (q : Pattern) (ha : d1880 q = 1) (hb : d208033 q = 1) : d24570 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d24570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d24570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1881 q = 1) (hb : d208033 q = 1) : d24571 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d24571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d24571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1889 q = 1) (hb : d208033 q = 1) : d24574 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d24574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56214 q ha hb
    | true =>
      simp only [d1889, d24574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56215 q ha hb
  have h5 (q : Pattern) (ha : d1890 q = 1) (hb : d208033 q = 1) : d24575 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d24575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d24575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1891 q = 1) (hb : d208033 q = 1) : d24576 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d24576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d24576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1892 q = 1) (hb : d208033 q = 1) : d24577 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d24577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1892, d24577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5680 q = 1) (hb : d208033 q = 1) : d5680 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d5681 q = 1) (hb : d208033 q = 1) : d24645 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5681, d24645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56245 q ha hb
    | true =>
      simp only [d5681, d24645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5682 q = 1) (hb : d208033 q = 1) : d24646 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5682, d24646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5682, d24646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5683 q = 1) (hb : d208033 q = 1) : d24647 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5683, d24647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5683, d24647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5684 q = 1) (hb : d208033 q = 1) : d24648 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5684, d24648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5684, d24648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5685 q = 1) (hb : d208033 q = 1) : d24649 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5685, d24649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5685, d24649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5686 q = 1) (hb : d208033 q = 1) : d24650 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5686, d24650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5686, d24650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro56247 (p : Pattern) (ha : d5692 p = 1) (hb : d208033 p = 1) : d24656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5687 q = 1) (hb : d208033 q = 1) : d24651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5687, d24651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56246 q ha hb
    | true =>
      simp only [d5687, d24651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5688 q = 1) (hb : d208033 q = 1) : d24652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5688, d24652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5688, d24652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5689 q = 1) (hb : d208033 q = 1) : d24653 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5689, d24653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5689, d24653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5690 q = 1) (hb : d208033 q = 1) : d24654 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5690, d24654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5690, d24654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5691 q = 1) (hb : d208033 q = 1) : d24655 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5691, d24655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5691, d24655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5692 q = 1) (hb : d208033 q = 1) : d24656 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5692, d24656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5692, d24656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro56248 (p : Pattern) (ha : d74749 p = 1) (hb : d208033 p = 1) : d211308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1914 q = 1) (hb : d208033 q = 1) : d24599 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1914, d24599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56243 q ha hb
    | true =>
      simp only [d1914, d24599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56244 q ha hb
  have h2 (q : Pattern) (ha : d4545 q = 1) (hb : d208033 q = 1) : d211304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4545, d211304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4545, d211304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5693 q = 1) (hb : d208033 q = 1) : d24657 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5693, d24657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56247 q ha hb
    | true =>
      simp only [d5693, d24657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5694 q = 1) (hb : d208033 q = 1) : d24658 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5694, d24658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5694, d24658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74746 q = 1) (hb : d208033 q = 1) : d211305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74746, d211305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74746, d211305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74747 q = 1) (hb : d208033 q = 1) : d211306 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74747, d211306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74747, d211306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74748 q = 1) (hb : d208033 q = 1) : d211307 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74748, d211307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74748, d211307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74749 q = 1) (hb : d208033 q = 1) : d211308 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74749, d211308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74749, d211308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro56249 (p : Pattern) (ha : d74755 p = 1) (hb : d208033 p = 1) : d211314 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d208033 q = 1) : d24366 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d24366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d24366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56207 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d208033 q = 1) : d24367 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d24367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, d24367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d208033 q = 1) : d24376 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d24376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56207 q ha hb
    | true =>
      simp only [d1640, d24376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56210 q ha hb
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d208033 q = 1) : d24377 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d24377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, d24377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1642 q = 1) (hb : d208033 q = 1) : d24378 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d24378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, d24378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74734 q = 1) (hb : d208033 q = 1) : d211292 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74734, d211292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56230 q ha hb
    | true =>
      simp only [d74734, d211292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56237 q ha hb
  have h7 (q : Pattern) (ha : d1839 q = 1) (hb : d208033 q = 1) : d24529 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, d24529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56211 q ha hb
    | true =>
      simp only [d1839, d24529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56212 q ha hb
  have h8 (q : Pattern) (ha : d74735 q = 1) (hb : d208033 q = 1) : d211293 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74735, d211293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74735, d211293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74736 q = 1) (hb : d208033 q = 1) : d211294 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74736, d211294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74736, d211294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d74737 q = 1) (hb : d208033 q = 1) : d211295 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74737, d211295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74737, d211295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74741 q = 1) (hb : d208033 q = 1) : d211299 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74741, d211299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74741, d211299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56238 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d208033 q = 1) : d24538 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d24538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, d24538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56213 q ha hb
  have h13 (q : Pattern) (ha : d74742 q = 1) (hb : d208033 q = 1) : d211300 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74742, d211300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74742, d211300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74743 q = 1) (hb : d208033 q = 1) : d211301 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74743, d211301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74743, d211301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d74744 q = 1) (hb : d208033 q = 1) : d211302 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74744, d211302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74744, d211302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d74745 q = 1) (hb : d208033 q = 1) : d211303 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74745, d211303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74745, d211303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74750 q = 1) (hb : d208033 q = 1) : d211309 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74750, d211309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74750, d211309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56248 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d208033 q = 1) : d24674 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, d24674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, d24674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56218 q ha hb
  have h19 (q : Pattern) (ha : d74751 q = 1) (hb : d208033 q = 1) : d211310 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74751, d211310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74751, d211310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d74752 q = 1) (hb : d208033 q = 1) : d211311 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74752, d211311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74752, d211311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d74753 q = 1) (hb : d208033 q = 1) : d211312 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74753, d211312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74753, d211312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d74754 q = 1) (hb : d208033 q = 1) : d211313 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74754, d211313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74754, d211313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d74755 q = 1) (hb : d208033 q = 1) : d211314 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74755, d211314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74755, d211314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
end NetHack.Soko22Hazard87
