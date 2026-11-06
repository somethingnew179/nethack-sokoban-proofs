import NetHack.Soko22Hazard87.EqIntroBlocks0121
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro30500 (p : Pattern) (selected : d32803 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32694 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30478 q selected
    | true =>
      simp only [d32694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32695 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d32695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d32696 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32697 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32802 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d32708 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30481 q selected
    | true =>
      simp only [d32708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d32709 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d32709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d32710 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d32711 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d32711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d32712 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d32803 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30501 (p : Pattern) (selected : d32807 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32708 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30481 q selected
    | true =>
      simp only [d32708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32709 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d32709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d32710 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32711 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32716 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30482 q selected
    | true =>
      simp only [d32716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d32717 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d32718 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d32719 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d32719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d32720 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d32738 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d32738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d32807 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d32807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30502 (p : Pattern) (selected : d32813 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32804 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30500 q selected
    | true =>
      simp only [d32804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30483 q selected
  have h2 (q : Pattern) (selected : d32805 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d32806 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32808 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30483 q selected
    | true =>
      simp only [d32808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30501 q selected
  have h5 (q : Pattern) (selected : d32809 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d32810 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d32811 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d32740 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30483 q selected
    | true =>
      simp only [d32740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30486 q selected
  have h9 (q : Pattern) (selected : d32741 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d32742 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d32745 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30486 q selected
    | true =>
      simp only [d32745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30487 q selected
  have h12 (q : Pattern) (selected : d32746 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d32747 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d32748 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d32748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d32812 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d32812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d32813 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d32813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro30503 (p : Pattern) (selected : d32819 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32814 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30502 q selected
    | true =>
      simp only [d32814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32815 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d32752 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30488 q selected
    | true =>
      simp only [d32752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d32753 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d32816 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d32817 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d32818 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d32818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d32819 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30504 (p : Pattern) (selected : d32821 p = 2) : d32687 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2 q = 2) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d338 q = 2) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d562 q = 2) : d307 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d562, d307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d562, d307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2163 q = 2) : d1997 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2163, d1997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2163, d1997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2164 q = 2) : d1998 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2164, d1998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2164, d1998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2165 q = 2) : d1999 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2165, d1999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2165, d1999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d32821 q = 2) : d32687 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d32821, d32687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d32821, d32687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro30505 (p : Pattern) (selected : d32827 p = 2) : d32693 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32822 q = 2) : d32688 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32822, d32688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30504 q selected
    | true =>
      simp only [d32822, d32688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32823 q = 2) : d32689 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32823, d32689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d32823, d32689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d32824 q = 2) : d32690 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32824, d32690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32824, d32690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32825 q = 2) : d32691 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32825, d32691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32825, d32691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32826 q = 2) : d32692 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32826, d32692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32826, d32692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d32827 q = 2) : d32693 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32827, d32693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32827, d32693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30506 (p : Pattern) (selected : d32832 p = 2) : d32698 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2 q = 2) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d338 q = 2) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d563 q = 2) : d308 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, d308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, d308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1691 q = 2) : d1523 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1691, d1523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1691, d1523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2167 q = 2) : d2001 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2167, d2001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2167, d2001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2168 q = 2) : d2002 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2168, d2002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2168, d2002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d32832 q = 2) : d32698 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d32832, d32698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d32832, d32698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro30507 (p : Pattern) (selected : d32835 p = 2) : d32701 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2 q = 2) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d338 q = 2) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d562 q = 2) : d307 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d562, d307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d562, d307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2163 q = 2) : d1997 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2163, d1997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2163, d1997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2164 q = 2) : d1998 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2164, d1998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2164, d1998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2179 q = 2) : d2013 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2179, d2013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2179, d2013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2180 q = 2) : d2014 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2180, d2014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2180, d2014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d32835 q = 2) : d32701 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d32835, d32701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d32835, d32701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30508 (p : Pattern) (selected : d32841 p = 2) : d32707 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32822 q = 2) : d32688 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32822, d32688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30504 q selected
    | true =>
      simp only [d32822, d32688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32823 q = 2) : d32689 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32823, d32689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d32823, d32689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d32824 q = 2) : d32690 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32824, d32690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32824, d32690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32825 q = 2) : d32691 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32825, d32691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32825, d32691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32826 q = 2) : d32692 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32826, d32692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32826, d32692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d32833 q = 2) : d32699 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32833, d32699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30504 q selected
    | true =>
      simp only [d32833, d32699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30506 q selected
  have h7 (q : Pattern) (selected : d10181 q = 2) : d10055 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10181, d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10181, d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10616 q selected
  have h8 (q : Pattern) (selected : d32834 q = 2) : d32700 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32834, d32700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d32834, d32700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d32836 q = 2) : d32702 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32836, d32702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30507 q selected
    | true =>
      simp only [d32836, d32702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d32837 q = 2) : d32703 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32837, d32703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d32837, d32703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d32838 q = 2) : d32704 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32838, d32704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d32838, d32704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d32839 q = 2) : d32705 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32839, d32705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d32839, d32705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d32840 q = 2) : d32706 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32840, d32706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d32840, d32706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d32841 q = 2) : d32707 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32841, d32707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32841, d32707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro30509 (p : Pattern) (selected : d32849 p = 2) : d32715 p = 1 := by
  have h0 (q : Pattern) (selected : d32833 q = 2) : d32699 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32833, d32699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30504 q selected
    | true =>
      simp only [d32833, d32699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30506 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d10181 q = 2) : d10055 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10181, d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10181, d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10616 q selected
  have h3 (q : Pattern) (selected : d32834 q = 2) : d32700 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32834, d32700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32834, d32700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32836 q = 2) : d32702 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32836, d32702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30507 q selected
    | true =>
      simp only [d32836, d32702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d32837 q = 2) : d32703 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32837, d32703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32837, d32703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d32838 q = 2) : d32704 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32838, d32704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32838, d32704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d32839 q = 2) : d32705 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32839, d32705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d32839, d32705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d32840 q = 2) : d32706 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32840, d32706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d32840, d32706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d2224 q = 2) : d2058 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2224, d2058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2224, d2058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1047 q selected
  have h10 (q : Pattern) (selected : d2209 q = 2) : d2043 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2209, d2043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2209, d2043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1048 q selected
  have h11 (q : Pattern) (selected : d2225 q = 2) : d2059 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2225, d2059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d2225, d2059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d2213 q = 2) : d2047 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2213, d2047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1049 q selected
    | true =>
      simp only [d2213, d2047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h13 (q : Pattern) (selected : d2214 q = 2) : d2048 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2214, d2048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d2214, d2048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h14 (q : Pattern) (selected : d2226 q = 2) : d2060 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2226, d2060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2226, d2060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10514 q = 2) : d10405 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10514, d10405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1047 q selected
    | true =>
      simp only [d10514, d10405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h16 (q : Pattern) (selected : d10515 q = 2) : d10406 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10515, d10406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1048 q selected
    | true =>
      simp only [d10515, d10406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h17 (q : Pattern) (selected : d10516 q = 2) : d10407 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10516, d10407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d10516, d10407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d10517 q = 2) : d10408 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10517, d10408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d10517, d10408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h19 (q : Pattern) (selected : d32847 q = 2) : d32713 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32847, d32713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d32847, d32713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d32848 q = 2) : d32714 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32848, d32714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d32848, d32714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h21 (q : Pattern) (selected : d32849 q = 2) : d32715 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32849, d32715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d32849, d32715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro30510 (p : Pattern) (selected : d32855 p = 2) : d32721 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32828 q = 2) : d32694 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32828, d32694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30505 q selected
    | true =>
      simp only [d32828, d32694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32829 q = 2) : d32695 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32829, d32695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d32829, d32695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d32830 q = 2) : d32696 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32830, d32696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32830, d32696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32831 q = 2) : d32697 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32831, d32697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32831, d32697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32842 q = 2) : d32708 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32842, d32708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30508 q selected
    | true =>
      simp only [d32842, d32708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d32843 q = 2) : d32709 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32843, d32709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32843, d32709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d32844 q = 2) : d32710 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32844, d32710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32844, d32710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d32845 q = 2) : d32711 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32845, d32711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d32845, d32711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d32846 q = 2) : d32712 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32846, d32712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32846, d32712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d32850 q = 2) : d32716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32850, d32716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30509 q selected
    | true =>
      simp only [d32850, d32716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d32851 q = 2) : d32717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32851, d32717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d32851, d32717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d32852 q = 2) : d32718 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32852, d32718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32852, d32718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d32853 q = 2) : d32719 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32853, d32719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d32853, d32719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d32854 q = 2) : d32720 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32854, d32720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d32854, d32720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d32855 q = 2) : d32721 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32855, d32721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d32855, d32721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30511 (p : Pattern) (selected : d32861 p = 2) : d32727 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32822 q = 2) : d32688 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32822, d32688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30504 q selected
    | true =>
      simp only [d32822, d32688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32823 q = 2) : d32689 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32823, d32689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d32823, d32689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d32824 q = 2) : d32690 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32824, d32690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32824, d32690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32825 q = 2) : d32691 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32825, d32691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32825, d32691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32826 q = 2) : d32692 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32826, d32692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32826, d32692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d32833 q = 2) : d32699 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32833, d32699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30504 q selected
    | true =>
      simp only [d32833, d32699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30506 q selected
  have h7 (q : Pattern) (selected : d10181 q = 2) : d10055 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10181, d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10181, d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10616 q selected
  have h8 (q : Pattern) (selected : d32834 q = 2) : d32700 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32834, d32700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d32834, d32700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d32856 q = 2) : d32722 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32856, d32722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30507 q selected
    | true =>
      simp only [d32856, d32722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1049 q selected
  have h10 (q : Pattern) (selected : d32857 q = 2) : d32723 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32857, d32723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d32857, d32723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d32858 q = 2) : d32724 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32858, d32724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d32858, d32724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d2213 q = 2) : d2047 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2213, d2047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1049 q selected
    | true =>
      simp only [d2213, d2047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d2214 q = 2) : d2048 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2214, d2048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d2214, d2048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d30248 q = 2) : d30103 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30248, d30103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d30248, d30103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d32859 q = 2) : d32725 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32859, d32725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d32859, d32725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d32860 q = 2) : d32726 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32860, d32726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d32860, d32726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d32861 q = 2) : d32727 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32861, d32727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32861, d32727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro30512 (p : Pattern) (selected : d32866 p = 2) : d32732 p = 1 := by
  have h0 (q : Pattern) (selected : d32833 q = 2) : d32699 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32833, d32699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30504 q selected
    | true =>
      simp only [d32833, d32699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30506 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d10181 q = 2) : d10055 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10181, d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10181, d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10616 q selected
  have h3 (q : Pattern) (selected : d32834 q = 2) : d32700 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32834, d32700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32834, d32700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32856 q = 2) : d32722 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32856, d32722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30507 q selected
    | true =>
      simp only [d32856, d32722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1049 q selected
  have h5 (q : Pattern) (selected : d32857 q = 2) : d32723 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32857, d32723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32857, d32723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d32858 q = 2) : d32724 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32858, d32724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32858, d32724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2213 q = 2) : d2047 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2213, d2047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1049 q selected
    | true =>
      simp only [d2213, d2047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d2214 q = 2) : d2048 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2214, d2048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2214, d2048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d30248 q = 2) : d30103 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30248, d30103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d30248, d30103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d32859 q = 2) : d32725 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32859, d32725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d32859, d32725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d32860 q = 2) : d32726 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32860, d32726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d32860, d32726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d2224 q = 2) : d2058 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2224, d2058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2224, d2058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1047 q selected
  have h13 (q : Pattern) (selected : d2209 q = 2) : d2043 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2209, d2043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2209, d2043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1048 q selected
  have h14 (q : Pattern) (selected : d2225 q = 2) : d2059 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2225, d2059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d2225, d2059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d2226 q = 2) : d2060 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2226, d2060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d2226, d2060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h16 (q : Pattern) (selected : d10514 q = 2) : d10405 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10514, d10405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1047 q selected
    | true =>
      simp only [d10514, d10405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h17 (q : Pattern) (selected : d10515 q = 2) : d10406 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10515, d10406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1048 q selected
    | true =>
      simp only [d10515, d10406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h18 (q : Pattern) (selected : d10516 q = 2) : d10407 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10516, d10407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d10516, d10407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d10517 q = 2) : d10408 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10517, d10408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d10517, d10408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h20 (q : Pattern) (selected : d32847 q = 2) : d32713 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32847, d32713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d32847, d32713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d32848 q = 2) : d32714 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32848, d32714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d32848, d32714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h22 (q : Pattern) (selected : d32866 q = 2) : d32732 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32866, d32732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d32866, d32732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  exact h22 p selected
theorem eqIntro30513 (p : Pattern) (selected : d32873 p = 2) : d32739 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32862 q = 2) : d32728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32862, d32728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30511 q selected
    | true =>
      simp only [d32862, d32728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32863 q = 2) : d32729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32863, d32729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d32863, d32729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d32864 q = 2) : d32730 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32864, d32730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32864, d32730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32865 q = 2) : d32731 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32865, d32731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32865, d32731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32867 q = 2) : d32733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32867, d32733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30512 q selected
    | true =>
      simp only [d32867, d32733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d32868 q = 2) : d32734 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32868, d32734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32868, d32734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d32869 q = 2) : d32735 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32869, d32735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32869, d32735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d32870 q = 2) : d32736 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32870, d32736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d32870, d32736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d32871 q = 2) : d32737 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32871, d32737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32871, d32737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d32850 q = 2) : d32716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32850, d32716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30509 q selected
    | true =>
      simp only [d32850, d32716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d32851 q = 2) : d32717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32851, d32717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d32851, d32717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d32852 q = 2) : d32718 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32852, d32718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32852, d32718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d32853 q = 2) : d32719 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32853, d32719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d32853, d32719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d32872 q = 2) : d32738 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32872, d32738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d32872, d32738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d32873 q = 2) : d32739 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32873, d32739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d32873, d32739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30514 (p : Pattern) (selected : d32878 p = 2) : d32744 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32867 q = 2) : d32733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32867, d32733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30512 q selected
    | true =>
      simp only [d32867, d32733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32868 q = 2) : d32734 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32868, d32734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d32868, d32734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d32869 q = 2) : d32735 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32869, d32735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32869, d32735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32870 q = 2) : d32736 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32870, d32736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32870, d32736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32877 q = 2) : d32743 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32877, d32743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32877, d32743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10521 q = 2) : d10412 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, d10412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10664 q selected
    | true =>
      simp only [d10521, d10412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10523 q = 2) : d10414 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10523, d10414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10523, d10414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15661 q = 2) : d15555 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15661, d15555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15661, d15555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d15662 q = 2) : d15556 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15662, d15556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15662, d15556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15663 q = 2) : d15557 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15663, d15557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d15663, d15557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d32878 q = 2) : d32744 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32878, d32744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32878, d32744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30515 (p : Pattern) (selected : d32885 p = 2) : d32751 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32874 q = 2) : d32740 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32874, d32740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30510 q selected
    | true =>
      simp only [d32874, d32740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30513 q selected
  have h2 (q : Pattern) (selected : d32875 q = 2) : d32741 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32875, d32741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32875, d32741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d32876 q = 2) : d32742 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32876, d32742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32876, d32742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32879 q = 2) : d32745 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32879, d32745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30513 q selected
    | true =>
      simp only [d32879, d32745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30514 q selected
  have h5 (q : Pattern) (selected : d32880 q = 2) : d32746 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32880, d32746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32880, d32746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d32881 q = 2) : d32747 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32881, d32747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32881, d32747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d32882 q = 2) : d32748 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32882, d32748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32882, d32748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d32883 q = 2) : d32749 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32883, d32749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d32883, d32749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d32884 q = 2) : d32750 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32884, d32750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d32884, d32750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d32885 q = 2) : d32751 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32885, d32751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d32885, d32751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30516 (p : Pattern) (selected : d32889 p = 2) : d32755 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32879 q = 2) : d32745 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32879, d32745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30513 q selected
    | true =>
      simp only [d32879, d32745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30514 q selected
  have h2 (q : Pattern) (selected : d32880 q = 2) : d32746 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32880, d32746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32880, d32746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d32881 q = 2) : d32747 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32881, d32747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32881, d32747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32883 q = 2) : d32749 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32883, d32749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32883, d32749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32888 q = 2) : d32754 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32888, d32754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32888, d32754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d32889 q = 2) : d32755 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32889, d32755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32889, d32755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30517 (p : Pattern) (selected : d32895 p = 2) : d32761 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32886 q = 2) : d32752 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32886, d32752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30515 q selected
    | true =>
      simp only [d32886, d32752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32887 q = 2) : d32753 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32887, d32753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32887, d32753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d32890 q = 2) : d32756 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32890, d32756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30516 q selected
    | true =>
      simp only [d32890, d32756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d32891 q = 2) : d32757 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32891, d32757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32891, d32757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d32892 q = 2) : d32758 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32892, d32758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32892, d32758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d32893 q = 2) : d32759 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32893, d32759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32893, d32759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d32894 q = 2) : d32760 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32894, d32760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d32894, d32760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d32895 q = 2) : d32761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32895, d32761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32895, d32761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30518 (p : Pattern) (selected : d32899 p = 2) : d32765 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32890 q = 2) : d32756 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32890, d32756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30516 q selected
    | true =>
      simp only [d32890, d32756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32891 q = 2) : d32757 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32891, d32757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32891, d32757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d32896 q = 2) : d32762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32896, d32762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32896, d32762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d32897 q = 2) : d32763 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32897, d32763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32897, d32763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32898 q = 2) : d32764 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32898, d32764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32898, d32764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d32899 q = 2) : d32765 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32899, d32765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32899, d32765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30519 (p : Pattern) (selected : d32905 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d32699 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30477 q selected
    | true =>
      simp only [d32699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30479 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d10055 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10598 q selected
  have h3 (q : Pattern) (selected : d32700 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32902 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d32903 q = 2) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d32904 q = 2) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d5238 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1015 q selected
  have h8 (q : Pattern) (selected : d5239 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d5239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d2047 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1015 q selected
    | true =>
      simp only [d2047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d2048 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d2048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d5243 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d5243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d2061 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d2061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h13 (q : Pattern) (selected : d5244 q = 2) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d5244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d5245 q = 2) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d5245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h15 (q : Pattern) (selected : d32905 q = 2) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d32905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30520 (p : Pattern) (selected : d32911 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32728 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30484 q selected
    | true =>
      simp only [d32728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32729 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d32729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d32730 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32731 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32733 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30485 q selected
    | true =>
      simp only [d32733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d32734 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d32735 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d32736 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d32736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d32737 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d32906 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30519 q selected
    | true =>
      simp only [d32906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d32907 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d32907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d32908 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d32909 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d32909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d32910 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d32910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d32911 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d32911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30521 (p : Pattern) (selected : d32915 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d32699 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30477 q selected
    | true =>
      simp only [d32699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30479 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d10055 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10598 q selected
  have h3 (q : Pattern) (selected : d32700 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5238 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1015 q selected
  have h5 (q : Pattern) (selected : d5239 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d5239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d32912 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2047 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1015 q selected
    | true =>
      simp only [d2047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d2048 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d30103 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d30103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d32913 q = 2) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d32913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d32914 q = 2) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d32914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d5243 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d5243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h13 (q : Pattern) (selected : d2061 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h14 (q : Pattern) (selected : d5244 q = 2) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d5244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d5245 q = 2) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d5245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h16 (q : Pattern) (selected : d32915 q = 2) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d32915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro30522 (p : Pattern) (selected : d32921 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32916 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30521 q selected
    | true =>
      simp only [d32916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32917 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d32917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d32918 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32919 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32920 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d32921 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30523 (p : Pattern) (selected : d32927 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32740 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30483 q selected
    | true =>
      simp only [d32740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30486 q selected
  have h2 (q : Pattern) (selected : d32741 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d32742 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32745 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30486 q selected
    | true =>
      simp only [d32745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30487 q selected
  have h5 (q : Pattern) (selected : d32746 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d32747 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d32748 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d32922 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30520 q selected
    | true =>
      simp only [d32922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30522 q selected
  have h9 (q : Pattern) (selected : d32923 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d32924 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d32925 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d32925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d32926 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d32926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d32927 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d32927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro30524 (p : Pattern) (selected : d32933 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32928 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30523 q selected
    | true =>
      simp only [d32928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32929 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d32930 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d32931 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32932 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d32933 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30525 (p : Pattern) (selected : d32939 p = 2) : d32771 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32789 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30496 q selected
    | true =>
      simp only [d32789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30497 q selected
  have h2 (q : Pattern) (selected : d32790 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d32791 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d32792 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d32799 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30498 q selected
    | true =>
      simp only [d32799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30499 q selected
  have h6 (q : Pattern) (selected : d32800 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d32801 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d32801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d32820 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30503 q selected
    | true =>
      simp only [d32820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30490 q selected
  have h9 (q : Pattern) (selected : d32900 q = 2) : d32766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32900, d32766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30517 q selected
    | true =>
      simp only [d32900, d32766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30518 q selected
  have h10 (q : Pattern) (selected : d32901 q = 2) : d32767 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32901, d32767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d32901, d32767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d32934 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30524 q selected
    | true =>
      simp only [d32934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d32935 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d32935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d32936 q = 2) : d32768 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32936, d32768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d32936, d32768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d32937 q = 2) : d32769 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32937, d32769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d32937, d32769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d32938 q = 2) : d32770 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32938, d32770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32938, d32770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d32939 q = 2) : d32771 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32939, d32771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32939, d32771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro30526 (p : Pattern) (selected : d32940 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32752 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30488 q selected
    | true =>
      simp only [d32752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32753 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d32756 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30489 q selected
    | true =>
      simp only [d32756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d32757 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d32758 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d32759 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d32785 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d32940 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d32940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30527 (p : Pattern) (selected : d32941 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32756 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30489 q selected
    | true =>
      simp only [d32756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32757 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d32762 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d32763 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32787 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d32941 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30528 (p : Pattern) (selected : d32946 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32752 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30488 q selected
    | true =>
      simp only [d32752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32753 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d32756 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30489 q selected
    | true =>
      simp only [d32756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d32757 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d32758 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d32793 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d32794 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d32794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d32946 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d32946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30529 (p : Pattern) (selected : d32947 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32756 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30489 q selected
    | true =>
      simp only [d32756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32757 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d32762 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d32796 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d32797 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d32947 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30530 (p : Pattern) (selected : d32951 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32814 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30502 q selected
    | true =>
      simp only [d32814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32815 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d32752 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30488 q selected
    | true =>
      simp only [d32752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d32753 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d32816 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d32817 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d32818 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d32818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d32951 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d32951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30531 (p : Pattern) (selected : d32953 p = 2) : d32774 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32886 q = 2) : d32752 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32886, d32752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30515 q selected
    | true =>
      simp only [d32886, d32752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32887 q = 2) : d32753 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32887, d32753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32887, d32753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d32890 q = 2) : d32756 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32890, d32756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30516 q selected
    | true =>
      simp only [d32890, d32756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d32891 q = 2) : d32757 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32891, d32757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32891, d32757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d32892 q = 2) : d32758 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32892, d32758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32892, d32758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d32893 q = 2) : d32759 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32893, d32759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32893, d32759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d32894 q = 2) : d32760 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32894, d32760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d32894, d32760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d32953 q = 2) : d32774 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32953, d32774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d32953, d32774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30532 (p : Pattern) (selected : d32954 p = 2) : d32775 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32890 q = 2) : d32756 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32890, d32756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30516 q selected
    | true =>
      simp only [d32890, d32756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32891 q = 2) : d32757 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32891, d32757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32891, d32757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d32896 q = 2) : d32762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32896, d32762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32896, d32762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d32897 q = 2) : d32763 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32897, d32763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32897, d32763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32898 q = 2) : d32764 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32898, d32764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32898, d32764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d32954 q = 2) : d32775 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32954, d32775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32954, d32775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30533 (p : Pattern) (selected : d32957 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32928 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30523 q selected
    | true =>
      simp only [d32928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32929 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d32930 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d32931 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32932 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d32957 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30534 (p : Pattern) (selected : d32963 p = 2) : d32781 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32789 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30496 q selected
    | true =>
      simp only [d32789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30497 q selected
  have h2 (q : Pattern) (selected : d32790 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d32791 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d32792 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d32799 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30498 q selected
    | true =>
      simp only [d32799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30499 q selected
  have h6 (q : Pattern) (selected : d32800 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d32801 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d32801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d32820 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30503 q selected
    | true =>
      simp only [d32820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30490 q selected
  have h9 (q : Pattern) (selected : d32900 q = 2) : d32766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32900, d32766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30517 q selected
    | true =>
      simp only [d32900, d32766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30518 q selected
  have h10 (q : Pattern) (selected : d32901 q = 2) : d32767 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32901, d32767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d32901, d32767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d32934 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30524 q selected
    | true =>
      simp only [d32934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d32935 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d32935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d32936 q = 2) : d32768 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32936, d32768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d32936, d32768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d32937 q = 2) : d32769 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32937, d32769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d32937, d32769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d32938 q = 2) : d32770 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32938, d32770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32938, d32770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d32942 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30526 q selected
    | true =>
      simp only [d32942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30527 q selected
  have h17 (q : Pattern) (selected : d32943 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d32944 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d32944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d32945 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d32948 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30528 q selected
    | true =>
      simp only [d32948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30529 q selected
  have h21 (q : Pattern) (selected : d32949 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d32950 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d32950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d32952 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30530 q selected
    | true =>
      simp only [d32952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30493 q selected
  have h24 (q : Pattern) (selected : d32955 q = 2) : d32776 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32955, d32776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30531 q selected
    | true =>
      simp only [d32955, d32776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30532 q selected
  have h25 (q : Pattern) (selected : d32956 q = 2) : d32777 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32956, d32777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d32956, d32777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d32958 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30533 q selected
    | true =>
      simp only [d32958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d32959 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d32959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d32960 q = 2) : d32778 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32960, d32778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d32960, d32778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d32961 q = 2) : d32779 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32961, d32779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d32961, d32779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d32962 q = 2) : d32780 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32962, d32780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d32962, d32780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d32963 q = 2) : d32781 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32963, d32781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d32963, d32781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro30535 (p : Pattern) (selected : d32970 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32766 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30490 q selected
    | true =>
      simp only [d32766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30491 q selected
  have h2 (q : Pattern) (selected : d32767 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d32768 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d32769 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d32770 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d32965 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30491 q selected
    | true =>
      simp only [d32965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d32966 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d32967 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d32967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d32968 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d32969 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d32970 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30536 (p : Pattern) (selected : d32976 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32965 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30491 q selected
    | true =>
      simp only [d32965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32966 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d32967 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d32968 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d32969 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d32971 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30494 q selected
    | true =>
      simp only [d32971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d32972 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d32973 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d32973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d32974 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d32975 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d32976 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30537 (p : Pattern) (selected : d32983 p = 2) : d290437 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32952 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30530 q selected
    | true =>
      simp only [d32952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30493 q selected
  have h2 (q : Pattern) (selected : d32955 q = 2) : d32776 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32955, d32776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30531 q selected
    | true =>
      simp only [d32955, d32776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30532 q selected
  have h3 (q : Pattern) (selected : d32956 q = 2) : d32777 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32956, d32777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d32956, d32777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32958 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30533 q selected
    | true =>
      simp only [d32958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32959 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d32959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d32960 q = 2) : d32778 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32960, d32778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32960, d32778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d32981 q = 2) : d32779 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32981, d32779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32981, d32779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d32982 q = 2) : d32780 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32982, d32780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32982, d32780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d32983 q = 2) : d290437 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32983, d290437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32983, d290437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro30538 (p : Pattern) (selected : d32985 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32971 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30494 q selected
    | true =>
      simp only [d32971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d32972 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d32973 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d32974 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d32975 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d32985 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30539 (p : Pattern) (selected : d33001 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32991 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30478 q selected
  have h2 (q : Pattern) (selected : d32694 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30478 q selected
    | true =>
      simp only [d32694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d32992 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d32992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32695 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32993 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d32994 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d32995 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d32996 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30481 q selected
  have h9 (q : Pattern) (selected : d32708 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30481 q selected
    | true =>
      simp only [d32708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d32997 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d32997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d32709 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d32709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d32998 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d32998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d32999 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d32999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d33000 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d33000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d33001 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d33001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30540 (p : Pattern) (selected : d33007 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32991 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30478 q selected
  have h2 (q : Pattern) (selected : d32694 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30478 q selected
    | true =>
      simp only [d32694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d32992 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d32992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32695 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32993 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d32994 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d32996 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30481 q selected
  have h8 (q : Pattern) (selected : d32708 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30481 q selected
    | true =>
      simp only [d32708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d32997 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d32997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d32709 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d32709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d32998 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d32998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d32999 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d32999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d33000 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d33000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d33002 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30482 q selected
  have h15 (q : Pattern) (selected : d32716 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30482 q selected
    | true =>
      simp only [d32716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d33003 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d33003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d32717 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d32717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d33004 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d33004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d33005 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d33005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d33006 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d33006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d33007 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d33007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro30541 (p : Pattern) (selected : d33012 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32996 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30481 q selected
  have h2 (q : Pattern) (selected : d32708 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30481 q selected
    | true =>
      simp only [d32708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d32997 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d32997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32709 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32998 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d32999 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d33002 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30482 q selected
  have h8 (q : Pattern) (selected : d32716 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30482 q selected
    | true =>
      simp only [d32716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d33003 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d33003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d32717 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d32717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d33004 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d33004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d33005 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d33005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d33006 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d33006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d33011 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d33011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d33012 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d33012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30542 (p : Pattern) (selected : d33026 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33017 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30484 q selected
  have h2 (q : Pattern) (selected : d32728 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30484 q selected
    | true =>
      simp only [d32728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d33018 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d33018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32729 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d33019 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33020 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d33021 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30485 q selected
  have h8 (q : Pattern) (selected : d32733 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30485 q selected
    | true =>
      simp only [d32733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d33022 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d33022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d32734 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d32734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d33023 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d33023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d33024 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d33024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d33025 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d33025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d33002 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30482 q selected
  have h15 (q : Pattern) (selected : d32716 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30482 q selected
    | true =>
      simp only [d32716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d33003 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d33003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d32717 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d32717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d33004 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d33004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d33005 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d33005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d33011 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d33011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d33026 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d33026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro30543 (p : Pattern) (selected : d33031 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33021 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30485 q selected
  have h2 (q : Pattern) (selected : d32733 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30485 q selected
    | true =>
      simp only [d32733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d33022 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d33022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32734 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d33023 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33024 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d33030 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d33030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15790 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10649 q selected
  have h9 (q : Pattern) (selected : d10412 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10649 q selected
    | true =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15791 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10414 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15792 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15793 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15794 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d33031 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d33031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30544 (p : Pattern) (selected : d33037 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33008 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30539 q selected
    | true =>
      simp only [d33008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30540 q selected
  have h2 (q : Pattern) (selected : d33009 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d33010 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d33013 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30540 q selected
    | true =>
      simp only [d33013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30541 q selected
  have h5 (q : Pattern) (selected : d33014 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33015 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d33016 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d33027 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30540 q selected
    | true =>
      simp only [d33027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30542 q selected
  have h9 (q : Pattern) (selected : d33028 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d33029 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d33032 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30542 q selected
    | true =>
      simp only [d33032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30543 q selected
  have h12 (q : Pattern) (selected : d33033 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d33034 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d33035 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d33035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d33036 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d33036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d33037 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d33037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro30545 (p : Pattern) (selected : d33042 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33027 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30540 q selected
    | true =>
      simp only [d33027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30542 q selected
  have h2 (q : Pattern) (selected : d33028 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d33029 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d33032 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30542 q selected
    | true =>
      simp only [d33032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30543 q selected
  have h5 (q : Pattern) (selected : d33033 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33034 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d33035 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d33040 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d33040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d33041 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d33041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d33042 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d33042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30546 (p : Pattern) (selected : d33048 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33038 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30544 q selected
    | true =>
      simp only [d33038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d33039 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d33043 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30545 q selected
    | true =>
      simp only [d33043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d33044 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d33045 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d33045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33046 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d33047 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d33047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d33048 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d33048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30547 (p : Pattern) (selected : d33050 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33032 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30542 q selected
    | true =>
      simp only [d33032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30543 q selected
  have h2 (q : Pattern) (selected : d33033 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d33034 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d33040 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d33049 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d33049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d33050 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30548 (p : Pattern) (selected : d33056 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33043 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30545 q selected
    | true =>
      simp only [d33043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d33044 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d33051 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30547 q selected
    | true =>
      simp only [d33051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d33052 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d33053 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d33053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33054 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d33055 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d33055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d33056 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d33056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30549 (p : Pattern) (selected : d33072 p = 2) : d33007 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33058 q = 2) : d32991 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33058, d32991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33058, d32991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30505 q selected
  have h2 (q : Pattern) (selected : d32828 q = 2) : d32694 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32828, d32694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30505 q selected
    | true =>
      simp only [d32828, d32694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d33059 q = 2) : d32992 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33059, d32992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d33059, d32992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32829 q = 2) : d32695 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32829, d32695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32829, d32695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d33060 q = 2) : d32993 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33060, d32993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33060, d32993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33061 q = 2) : d32994 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33061, d32994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33061, d32994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d33062 q = 2) : d32996 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33062, d32996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33062, d32996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30508 q selected
  have h8 (q : Pattern) (selected : d32842 q = 2) : d32708 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32842, d32708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30508 q selected
    | true =>
      simp only [d32842, d32708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d33063 q = 2) : d32997 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33063, d32997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d33063, d32997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d32843 q = 2) : d32709 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32843, d32709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d32843, d32709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d33064 q = 2) : d32998 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33064, d32998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d33064, d32998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d33065 q = 2) : d32999 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33065, d32999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d33065, d32999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d33066 q = 2) : d33000 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33066, d33000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d33066, d33000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d33067 q = 2) : d33002 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33067, d33002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33067, d33002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30509 q selected
  have h15 (q : Pattern) (selected : d32850 q = 2) : d32716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32850, d32716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30509 q selected
    | true =>
      simp only [d32850, d32716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d33068 q = 2) : d33003 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33068, d33003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d33068, d33003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d32851 q = 2) : d32717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32851, d32717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d32851, d32717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d33069 q = 2) : d33004 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33069, d33004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d33069, d33004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d33070 q = 2) : d33005 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33070, d33005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d33070, d33005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d33071 q = 2) : d33006 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33071, d33006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d33071, d33006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d33072 q = 2) : d33007 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33072, d33007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d33072, d33007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro30550 (p : Pattern) (selected : d33083 p = 2) : d33026 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33073 q = 2) : d33017 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33073, d33017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33073, d33017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30511 q selected
  have h2 (q : Pattern) (selected : d32862 q = 2) : d32728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32862, d32728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30511 q selected
    | true =>
      simp only [d32862, d32728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d33074 q = 2) : d33018 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33074, d33018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d33074, d33018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32863 q = 2) : d32729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32863, d32729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32863, d32729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d33075 q = 2) : d33019 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33075, d33019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33075, d33019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33076 q = 2) : d33020 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33076, d33020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33076, d33020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d33077 q = 2) : d33021 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33077, d33021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33077, d33021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30512 q selected
  have h8 (q : Pattern) (selected : d32867 q = 2) : d32733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32867, d32733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30512 q selected
    | true =>
      simp only [d32867, d32733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d33078 q = 2) : d33022 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33078, d33022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d33078, d33022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d32868 q = 2) : d32734 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32868, d32734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d32868, d32734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d33079 q = 2) : d33023 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33079, d33023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d33079, d33023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d33080 q = 2) : d33024 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33080, d33024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d33080, d33024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d33081 q = 2) : d33025 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33081, d33025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d33081, d33025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d33067 q = 2) : d33002 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33067, d33002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33067, d33002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30509 q selected
  have h15 (q : Pattern) (selected : d32850 q = 2) : d32716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32850, d32716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30509 q selected
    | true =>
      simp only [d32850, d32716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d33068 q = 2) : d33003 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33068, d33003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d33068, d33003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d32851 q = 2) : d32717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32851, d32717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d32851, d32717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d33069 q = 2) : d33004 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33069, d33004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d33069, d33004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d33070 q = 2) : d33005 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33070, d33005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d33070, d33005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d33082 q = 2) : d33011 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33082, d33011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d33082, d33011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d33083 q = 2) : d33026 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33083, d33026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d33083, d33026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro30551 (p : Pattern) (selected : d33088 p = 2) : d33031 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33077 q = 2) : d33021 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33077, d33021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33077, d33021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30512 q selected
  have h2 (q : Pattern) (selected : d32867 q = 2) : d32733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32867, d32733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30512 q selected
    | true =>
      simp only [d32867, d32733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d33078 q = 2) : d33022 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33078, d33022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d33078, d33022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32868 q = 2) : d32734 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32868, d32734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32868, d32734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d33079 q = 2) : d33023 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33079, d33023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33079, d33023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33080 q = 2) : d33024 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33080, d33024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33080, d33024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d33087 q = 2) : d33030 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33087, d33030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d33087, d33030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15844 q = 2) : d15790 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15844, d15790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15844, d15790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10664 q selected
  have h9 (q : Pattern) (selected : d10521 q = 2) : d10412 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, d10412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10664 q selected
    | true =>
      simp only [d10521, d10412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15845 q = 2) : d15791 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15845, d15791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15845, d15791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10523 q = 2) : d10414 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10523, d10414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10523, d10414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15846 q = 2) : d15792 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15846, d15792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15846, d15792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15847 q = 2) : d15793 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15847, d15793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15847, d15793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15848 q = 2) : d15794 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15848, d15794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15848, d15794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d33088 q = 2) : d33031 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33088, d33031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d33088, d33031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30552 (p : Pattern) (selected : d33095 p = 2) : d33042 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33084 q = 2) : d33027 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33084, d33027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30549 q selected
    | true =>
      simp only [d33084, d33027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30550 q selected
  have h2 (q : Pattern) (selected : d33085 q = 2) : d33028 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33085, d33028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33085, d33028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d33086 q = 2) : d33029 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33086, d33029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33086, d33029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d33089 q = 2) : d33032 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33089, d33032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30550 q selected
    | true =>
      simp only [d33089, d33032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30551 q selected
  have h5 (q : Pattern) (selected : d33090 q = 2) : d33033 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33090, d33033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33090, d33033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33091 q = 2) : d33034 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33091, d33034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33091, d33034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d33092 q = 2) : d33035 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33092, d33035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33092, d33035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d33093 q = 2) : d33040 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33093, d33040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d33093, d33040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d33094 q = 2) : d33041 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33094, d33041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d33094, d33041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d33095 q = 2) : d33042 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33095, d33042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d33095, d33042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30553 (p : Pattern) (selected : d33099 p = 2) : d33050 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33089 q = 2) : d33032 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33089, d33032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30550 q selected
    | true =>
      simp only [d33089, d33032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30551 q selected
  have h2 (q : Pattern) (selected : d33090 q = 2) : d33033 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33090, d33033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33090, d33033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d33091 q = 2) : d33034 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33091, d33034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33091, d33034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d33093 q = 2) : d33040 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33093, d33040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33093, d33040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d33098 q = 2) : d33049 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33098, d33049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d33098, d33049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d33099 q = 2) : d33050 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33099, d33050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33099, d33050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30554 (p : Pattern) (selected : d33105 p = 2) : d33056 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33096 q = 2) : d33043 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33096, d33043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30552 q selected
    | true =>
      simp only [d33096, d33043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d33097 q = 2) : d33044 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33097, d33044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33097, d33044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d33100 q = 2) : d33051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33100, d33051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30553 q selected
    | true =>
      simp only [d33100, d33051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d33101 q = 2) : d33052 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33101, d33052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33101, d33052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d33102 q = 2) : d33053 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33102, d33053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d33102, d33053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33103 q = 2) : d33054 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33103, d33054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33103, d33054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d33104 q = 2) : d33055 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33104, d33055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d33104, d33055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d33105 q = 2) : d33056 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33105, d33056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d33105, d33056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30555 (p : Pattern) (selected : d33109 p = 2) : d33146 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33100 q = 2) : d33051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33100, d33051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30553 q selected
    | true =>
      simp only [d33100, d33051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d33101 q = 2) : d33052 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33101, d33052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33101, d33052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d33106 q = 2) : d33143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33106, d33143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d33106, d33143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d33107 q = 2) : d33144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33107, d33144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33107, d33144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d33108 q = 2) : d33145 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33108, d33145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d33108, d33145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d33109 q = 2) : d33146 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33109, d33146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33109, d33146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30556 (p : Pattern) (selected : d33117 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33017 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30484 q selected
  have h2 (q : Pattern) (selected : d32728 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30484 q selected
    | true =>
      simp only [d32728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d33018 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d33018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32729 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d33019 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33020 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d33021 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30485 q selected
  have h8 (q : Pattern) (selected : d32733 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30485 q selected
    | true =>
      simp only [d32733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d33022 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d33022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d32734 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d32734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d33023 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d33023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d33024 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d33024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d33025 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d33025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d33112 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30519 q selected
  have h15 (q : Pattern) (selected : d32906 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30519 q selected
    | true =>
      simp only [d32906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d33113 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d33113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d32907 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d32907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d33114 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d33114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d33115 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d33115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d33116 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d33116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d33117 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d33117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro30557 (p : Pattern) (selected : d33123 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33118 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30521 q selected
  have h2 (q : Pattern) (selected : d32916 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30521 q selected
    | true =>
      simp only [d32916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d33119 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d33119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32917 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d33120 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33121 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d33122 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d33122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d33123 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d33123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30558 (p : Pattern) (selected : d33129 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33027 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30540 q selected
    | true =>
      simp only [d33027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30542 q selected
  have h2 (q : Pattern) (selected : d33028 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d33029 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d33032 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30542 q selected
    | true =>
      simp only [d33032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30543 q selected
  have h5 (q : Pattern) (selected : d33033 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33034 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d33035 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d33124 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30556 q selected
    | true =>
      simp only [d33124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30557 q selected
  have h9 (q : Pattern) (selected : d33125 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d33126 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d33127 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d33127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d33128 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d33128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d33129 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d33129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro30559 (p : Pattern) (selected : d33135 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33130 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30558 q selected
    | true =>
      simp only [d33130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d33131 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d33132 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d33132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d33133 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d33134 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d33134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d33135 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30560 (p : Pattern) (selected : d33141 p = 2) : d290448 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33057 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30546 q selected
    | true =>
      simp only [d33057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30548 q selected
  have h2 (q : Pattern) (selected : d33110 q = 2) : d290443 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33110, d290443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30554 q selected
    | true =>
      simp only [d33110, d290443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30555 q selected
  have h3 (q : Pattern) (selected : d33111 q = 2) : d290444 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33111, d290444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d33111, d290444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d33136 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30559 q selected
    | true =>
      simp only [d33136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d33137 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d33137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d33138 q = 2) : d290445 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33138, d290445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33138, d290445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d33139 q = 2) : d290446 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33139, d290446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33139, d290446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d33140 q = 2) : d290447 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33140, d290447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33140, d290447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d33141 q = 2) : d290448 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33141, d290448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33141, d290448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro30561 (p : Pattern) (selected : d33146 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33051 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30547 q selected
    | true =>
      simp only [d33051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d33052 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d33143 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d33143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d33144 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d33145 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d33145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d33146 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30562 (p : Pattern) (selected : d33152 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33147 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30561 q selected
    | true =>
      simp only [d33147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d33148 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d33149 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d33149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d33150 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d33151 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33152 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30563 (p : Pattern) (selected : d33158 p = 2) : d290454 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d32772 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30492 q selected
  have h2 (q : Pattern) (selected : d32773 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d32773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d32773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d32782 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30492 q selected
    | true =>
      simp only [d32782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30495 q selected
  have h4 (q : Pattern) (selected : d32783 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d32783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32784 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d32784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d32784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d32964 q = 2) : d32782 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32964, d32782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30525 q selected
    | true =>
      simp only [d32964, d32782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30534 q selected
  have h7 (q : Pattern) (selected : d32977 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30535 q selected
    | true =>
      simp only [d32977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30536 q selected
  have h8 (q : Pattern) (selected : d32978 q = 2) : d32783 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d32978, d32783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d32978, d32783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d32979 q = 2) : d290435 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d32979, d290435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d32979, d290435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d32980 q = 2) : d290436 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d32980, d290436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d32980, d290436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d32984 q = 2) : d290438 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32984, d290438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32984, d290438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30537 q selected
  have h12 (q : Pattern) (selected : d32986 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30538 q selected
  have h13 (q : Pattern) (selected : d32987 q = 2) : d290439 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d32987, d290439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d32987, d290439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d32988 q = 2) : d290440 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d32988, d290440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d32988, d290440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d32989 q = 2) : d290441 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d32989, d290441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d32989, d290441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d32990 q = 2) : d290442 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d32990, d290442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d32990, d290442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d33142 q = 2) : d290449 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33142, d290449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33142, d290449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30560 q selected
  have h18 (q : Pattern) (selected : d33153 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30562 q selected
  have h19 (q : Pattern) (selected : d33154 q = 2) : d290450 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33154, d290450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d33154, d290450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d33155 q = 2) : d290451 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d33155, d290451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d33155, d290451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d33156 q = 2) : d290452 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d33156, d290452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d33156, d290452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d33157 q = 2) : d290453 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d33157, d290453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d33157, d290453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d33158 q = 2) : d290454 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d33158, d290454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d33158, d290454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro30564 (p : Pattern) (selected : d33164 p = 2) : d290460 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33159 q = 2) : d290455 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d33159, d290455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33159, d290455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30563 q selected
  have h2 (q : Pattern) (selected : d33160 q = 2) : d290456 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d33160, d290456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33160, d290456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d33161 q = 2) : d290457 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d33161, d290457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33161, d290457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d33162 q = 2) : d290458 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d33162, d290458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33162, d290458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d33163 q = 2) : d290459 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d33163, d290459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33163, d290459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33164 q = 2) : d290460 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d33164, d290460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33164, d290460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30565 (p : Pattern) (selected : d33170 p = 2) : d290466 p = 1 := by
  have h0 (q : Pattern) (selected : d31230 q = 2) : d282120 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d31230, d282120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30163 q selected
    | true =>
      simp only [d31230, d282120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30225 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d31619 q = 2) : d282147 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d31619, d282147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d31619, d282147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30300 q selected
  have h3 (q : Pattern) (selected : d31620 q = 2) : d282148 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d31620, d282148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d31620, d282148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d32137 q = 2) : d290402 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d32137, d290402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d32137, d290402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30385 q selected
  have h5 (q : Pattern) (selected : d32138 q = 2) : d290403 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d32138, d290403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d32138, d290403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d32139 q = 2) : d290404 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d32139, d290404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d32139, d290404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d32683 q = 2) : d290431 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d32683, d290431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d32683, d290431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30476 q selected
  have h8 (q : Pattern) (selected : d32684 q = 2) : d290432 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d32684, d290432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d32684, d290432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d32685 q = 2) : d290433 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d32685, d290433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d32685, d290433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d32686 q = 2) : d290434 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d32686, d290434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d32686, d290434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d33165 q = 2) : d290461 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d33165, d290461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d33165, d290461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30564 q selected
  have h12 (q : Pattern) (selected : d33166 q = 2) : d290462 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d33166, d290462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d33166, d290462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d33167 q = 2) : d290463 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d33167, d290463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d33167, d290463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d33168 q = 2) : d290464 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d33168, d290464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d33168, d290464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d33169 q = 2) : d290465 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d33169, d290465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d33169, d290465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d33170 q = 2) : d290466 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d33170, d290466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d33170, d290466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro30566 (p : Pattern) (selected : d33176 p = 2) : d290472 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33171 q = 2) : d290467 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d33171, d290467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30565 q selected
    | true =>
      simp only [d33171, d290467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d33172 q = 2) : d290468 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d33172, d290468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d33172, d290468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d33173 q = 2) : d290469 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d33173, d290469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d33173, d290469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d33174 q = 2) : d290470 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d33174, d290470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33174, d290470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d33175 q = 2) : d290471 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d33175, d290471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d33175, d290471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d33176 q = 2) : d290472 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d33176, d290472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33176, d290472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30567 (p : Pattern) (selected : d33182 p = 2) : d290478 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33177 q = 2) : d290473 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d33177, d290473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30566 q selected
    | true =>
      simp only [d33177, d290473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d33178 q = 2) : d290474 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d33178, d290474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d33178, d290474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d33179 q = 2) : d290475 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d33179, d290475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d33179, d290475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d33180 q = 2) : d290476 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d33180, d290476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33180, d290476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d33181 q = 2) : d290477 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d33181, d290477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d33181, d290477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d33182 q = 2) : d290478 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d33182, d290478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33182, d290478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30568 (p : Pattern) (selected : d33188 p = 2) : d290484 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33183 q = 2) : d290479 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d33183, d290479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30567 q selected
    | true =>
      simp only [d33183, d290479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d33184 q = 2) : d290480 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d33184, d290480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d33184, d290480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d33185 q = 2) : d290481 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d33185, d290481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d33185, d290481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d33186 q = 2) : d290482 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d33186, d290482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33186, d290482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d33187 q = 2) : d290483 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d33187, d290483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d33187, d290483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d33188 q = 2) : d290484 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d33188, d290484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33188, d290484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30569 (p : Pattern) (selected : d33194 p = 2) : d290490 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33189 q = 2) : d290485 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d33189, d290485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30568 q selected
    | true =>
      simp only [d33189, d290485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d33190 q = 2) : d290486 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d33190, d290486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d33190, d290486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d33191 q = 2) : d290487 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d33191, d290487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d33191, d290487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d33192 q = 2) : d290488 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d33192, d290488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33192, d290488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d33193 q = 2) : d290489 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d33193, d290489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d33193, d290489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d33194 q = 2) : d290490 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d33194, d290490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33194, d290490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30570 (p : Pattern) (selected : d33200 p = 2) : d290496 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33195 q = 2) : d290491 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d33195, d290491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30569 q selected
    | true =>
      simp only [d33195, d290491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d33196 q = 2) : d290492 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d33196, d290492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d33196, d290492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d33197 q = 2) : d290493 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d33197, d290493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d33197, d290493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d33198 q = 2) : d290494 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d33198, d290494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33198, d290494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d33199 q = 2) : d290495 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d33199, d290495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d33199, d290495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d33200 q = 2) : d290496 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d33200, d290496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33200, d290496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30571 (p : Pattern) (selected : d33206 p = 2) : d290502 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33201 q = 2) : d290497 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d33201, d290497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30570 q selected
    | true =>
      simp only [d33201, d290497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d33202 q = 2) : d290498 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d33202, d290498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d33202, d290498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d33203 q = 2) : d290499 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d33203, d290499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d33203, d290499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d33204 q = 2) : d290500 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d33204, d290500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33204, d290500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d33205 q = 2) : d290501 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d33205, d290501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d33205, d290501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d33206 q = 2) : d290502 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d33206, d290502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33206, d290502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30572 (p : Pattern) (selected : d33212 p = 2) : d290508 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d33207 q = 2) : d290503 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d33207, d290503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30571 q selected
    | true =>
      simp only [d33207, d290503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d33208 q = 2) : d290504 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d33208, d290504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d33208, d290504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d33209 q = 2) : d290505 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d33209, d290505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d33209, d290505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d33210 q = 2) : d290506 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d33210, d290506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d33210, d290506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d33211 q = 2) : d290507 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d33211, d290507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d33211, d290507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d33212 q = 2) : d290508 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d33212, d290508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d33212, d290508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30573 (p : Pattern) (selected : d290510 p = 0) : d292129 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d313 q = 0) : d52112 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro234 q selected
    | true =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314 q = 0) : d52113 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d25433 q = 0) : d198756 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d198756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18742 q selected
    | true =>
      simp only [d25433, d198756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25434 q = 0) : d198757 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d198757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25434, d198757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290509 q = 0) : d292128 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d290509, d292128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290509, d292128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290510 q = 0) : d292129 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d290510, d292129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290510, d292129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30574 (p : Pattern) (selected : d290516 p = 0) : d292135 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d134 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d290515 q = 0) : d292134 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d290515, d292134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290515, d292134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290516 q = 0) : d292135 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d290516, d292135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290516, d292135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro30575 (p : Pattern) (selected : d290523 p = 0) : d292142 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290511 q = 0) : d292130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290511, d292130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30573 q selected
    | true =>
      simp only [d290511, d292130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290512 q = 0) : d292131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290512, d292131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290512, d292131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d290513 q = 0) : d292132 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290513, d292132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290513, d292132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290514 q = 0) : d292133 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290514, d292133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290514, d292133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290517 q = 0) : d292136 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290517, d292136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30574 q selected
    | true =>
      simp only [d290517, d292136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290518 q = 0) : d292137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290518, d292137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290518, d292137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290519 q = 0) : d292138 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290519, d292138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290519, d292138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290520 q = 0) : d292139 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290520, d292139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290520, d292139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290521 q = 0) : d292140 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290521, d292140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290521, d292140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d152858 q = 0) : d154955 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152858, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13724 q selected
    | true =>
      simp only [d152858, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d152859 q = 0) : d154956 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152859, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d152859, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d152860 q = 0) : d154957 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d152860, d154957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152860, d154957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d152861 q = 0) : d154958 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d152861, d154958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d152861, d154958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d290522 q = 0) : d292141 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290522, d292141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290522, d292141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d290523 q = 0) : d292142 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d290523, d292142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290523, d292142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30576 (p : Pattern) (selected : d290529 p = 0) : d292148 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290524 q = 0) : d292143 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290524, d292143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30575 q selected
    | true =>
      simp only [d290524, d292143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13742 q selected
  have h2 (q : Pattern) (selected : d290525 q = 0) : d292144 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290525, d292144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290525, d292144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290526 q = 0) : d292145 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290526, d292145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290526, d292145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152969 q = 0) : d155066 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d152969, d155066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13742 q selected
    | true =>
      simp only [d152969, d155066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13725 q selected
  have h5 (q : Pattern) (selected : d152970 q = 0) : d155067 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d152970, d155067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152970, d155067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152971 q = 0) : d155068 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d152971, d155068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152971, d155068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290527 q = 0) : d292146 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290527, d292146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290527, d292146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d152864 q = 0) : d154961 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d152864, d154961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13725 q selected
    | true =>
      simp only [d152864, d154961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d152865 q = 0) : d154962 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d152865, d154962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152865, d154962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d152866 q = 0) : d154963 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d152866, d154963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152866, d154963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d152972 q = 0) : d155069 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d152972, d155069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d152972, d155069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d290528 q = 0) : d292147 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d290528, d292147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290528, d292147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d290529 q = 0) : d292148 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d290529, d292148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d290529, d292148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro30577 (p : Pattern) (selected : d290535 p = 0) : d292154 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290530 q = 0) : d292149 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290530, d292149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30576 q selected
    | true =>
      simp only [d290530, d292149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290531 q = 0) : d292150 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290531, d292150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290531, d292150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152975 q = 0) : d155072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13743 q selected
    | true =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152976 q = 0) : d155073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290532 q = 0) : d292151 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290532, d292151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290532, d292151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290533 q = 0) : d292152 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290533, d292152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290533, d292152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290534 q = 0) : d292153 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290534, d292153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290534, d292153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290535 q = 0) : d292154 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290535, d292154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290535, d292154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30578 (p : Pattern) (selected : d290541 p = 0) : d292160 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153112 q = 0) : d155167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153112, d155167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13768 q selected
    | true =>
      simp only [d153112, d155167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13739 q selected
  have h2 (q : Pattern) (selected : d153113 q = 0) : d155168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153113, d155168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153113, d155168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153114 q = 0) : d155169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153114, d155169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153114, d155169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153115 q = 0) : d155170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153115, d155170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153115, d155170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153119 q = 0) : d155174 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153119, d155174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13769 q selected
    | true =>
      simp only [d153119, d155174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13740 q selected
  have h6 (q : Pattern) (selected : d153120 q = 0) : d155175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153120, d155175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153120, d155175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153121 q = 0) : d155176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153121, d155176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153121, d155176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290536 q = 0) : d292155 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290536, d292155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30577 q selected
    | true =>
      simp only [d290536, d292155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13744 q selected
  have h9 (q : Pattern) (selected : d153170 q = 0) : d155078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153170, d155078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13778 q selected
    | true =>
      simp only [d153170, d155078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13748 q selected
  have h10 (q : Pattern) (selected : d290537 q = 0) : d292156 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290537, d292156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290537, d292156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153176 q = 0) : d155210 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153176, d155210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13779 q selected
    | true =>
      simp only [d153176, d155210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153177 q = 0) : d155211 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153177, d155211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153177, d155211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d290538 q = 0) : d292157 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290538, d292157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d290538, d292157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d290539 q = 0) : d292158 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290539, d292158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290539, d292158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d290540 q = 0) : d292159 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290540, d292159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290540, d292159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d290541 q = 0) : d292160 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290541, d292160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290541, d292160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro30579 (p : Pattern) (selected : d290542 p = 0) : d292161 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290530 q = 0) : d292149 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290530, d292149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30576 q selected
    | true =>
      simp only [d290530, d292149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290531 q = 0) : d292150 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290531, d292150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290531, d292150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152975 q = 0) : d155072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13743 q selected
    | true =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152976 q = 0) : d155073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290532 q = 0) : d292151 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290532, d292151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290532, d292151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290533 q = 0) : d292152 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290533, d292152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290533, d292152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290534 q = 0) : d292153 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290534, d292153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290534, d292153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290542 q = 0) : d292161 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290542, d292161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290542, d292161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30580 (p : Pattern) (selected : d290548 p = 0) : d292167 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153112 q = 0) : d155167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153112, d155167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13768 q selected
    | true =>
      simp only [d153112, d155167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13739 q selected
  have h2 (q : Pattern) (selected : d153113 q = 0) : d155168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153113, d155168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153113, d155168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153114 q = 0) : d155169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153114, d155169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153114, d155169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153115 q = 0) : d155170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153115, d155170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153115, d155170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153119 q = 0) : d155174 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153119, d155174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13769 q selected
    | true =>
      simp only [d153119, d155174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13740 q selected
  have h6 (q : Pattern) (selected : d153120 q = 0) : d155175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153120, d155175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153120, d155175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d153121 q = 0) : d155176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153121, d155176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153121, d155176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290536 q = 0) : d292155 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290536, d292155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30577 q selected
    | true =>
      simp only [d290536, d292155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13744 q selected
  have h9 (q : Pattern) (selected : d153170 q = 0) : d155078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153170, d155078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13778 q selected
    | true =>
      simp only [d153170, d155078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13748 q selected
  have h10 (q : Pattern) (selected : d290537 q = 0) : d292156 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290537, d292156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290537, d292156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153176 q = 0) : d155210 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153176, d155210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13779 q selected
    | true =>
      simp only [d153176, d155210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d153177 q = 0) : d155211 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153177, d155211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d153177, d155211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d290538 q = 0) : d292157 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290538, d292157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d290538, d292157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d290539 q = 0) : d292158 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290539, d292158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290539, d292158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d290540 q = 0) : d292159 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290540, d292159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290540, d292159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d153183 q = 0) : d155217 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153183, d155217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13781 q selected
    | true =>
      simp only [d153183, d155217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13750 q selected
  have h17 (q : Pattern) (selected : d153184 q = 0) : d155218 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153184, d155218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153184, d155218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d153185 q = 0) : d155219 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153185, d155219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d153185, d155219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d153186 q = 0) : d155220 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153186, d155220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153186, d155220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d153188 q = 0) : d155222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153188, d155222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13782 q selected
    | true =>
      simp only [d153188, d155222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13751 q selected
  have h21 (q : Pattern) (selected : d153189 q = 0) : d155223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153189, d155223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153189, d155223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d153190 q = 0) : d155224 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153190, d155224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d153190, d155224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d290543 q = 0) : d292162 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290543, d292162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30579 q selected
    | true =>
      simp only [d290543, d292162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13752 q selected
  have h24 (q : Pattern) (selected : d153194 q = 0) : d155094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153194, d155094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13784 q selected
    | true =>
      simp only [d153194, d155094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13753 q selected
  have h25 (q : Pattern) (selected : d290544 q = 0) : d292163 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290544, d292163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d290544, d292163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d153197 q = 0) : d155229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153197, d155229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13785 q selected
    | true =>
      simp only [d153197, d155229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d153198 q = 0) : d155230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153198, d155230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d153198, d155230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d290545 q = 0) : d292164 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290545, d292164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d290545, d292164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d290546 q = 0) : d292165 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290546, d292165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d290546, d292165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d290547 q = 0) : d292166 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290547, d292166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d290547, d292166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d290548 q = 0) : d292167 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290548, d292167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d290548, d292167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro30581 (p : Pattern) (selected : d290555 p = 0) : d292174 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290543 q = 0) : d292162 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290543, d292162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30579 q selected
    | true =>
      simp only [d290543, d292162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13752 q selected
  have h2 (q : Pattern) (selected : d153194 q = 0) : d155094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153194, d155094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13784 q selected
    | true =>
      simp only [d153194, d155094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13753 q selected
  have h3 (q : Pattern) (selected : d290544 q = 0) : d292163 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290544, d292163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290544, d292163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153197 q = 0) : d155229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153197, d155229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13785 q selected
    | true =>
      simp only [d153197, d155229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153198 q = 0) : d155230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153198, d155230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153198, d155230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290545 q = 0) : d292164 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290545, d292164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290545, d292164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290553 q = 0) : d292172 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290553, d292172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290553, d292172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290554 q = 0) : d292173 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290554, d292173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290554, d292173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d290555 q = 0) : d292174 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290555, d292174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290555, d292174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro30582 (p : Pattern) (selected : d290571 p = 0) : d292190 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290561 q = 0) : d292180 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290561, d292180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290561, d292180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30573 q selected
  have h2 (q : Pattern) (selected : d290511 q = 0) : d292130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290511, d292130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30573 q selected
    | true =>
      simp only [d290511, d292130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d290562 q = 0) : d292181 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290562, d292181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290562, d292181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290512 q = 0) : d292131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290512, d292131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290512, d292131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290563 q = 0) : d292182 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290563, d292182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290563, d292182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290564 q = 0) : d292183 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290564, d292183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290564, d292183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290565 q = 0) : d292184 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290565, d292184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290565, d292184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30574 q selected
  have h8 (q : Pattern) (selected : d290517 q = 0) : d292136 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290517, d292136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30574 q selected
    | true =>
      simp only [d290517, d292136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290566 q = 0) : d292185 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290566, d292185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290566, d292185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290518 q = 0) : d292137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290518, d292137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290518, d292137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d290567 q = 0) : d292186 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290567, d292186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290567, d292186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d290568 q = 0) : d292187 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290568, d292187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d290568, d292187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d290569 q = 0) : d292188 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290569, d292188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290569, d292188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d152899 q = 0) : d154996 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152899, d154996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152899, d154996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13724 q selected
  have h15 (q : Pattern) (selected : d152858 q = 0) : d154955 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152858, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13724 q selected
    | true =>
      simp only [d152858, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d152900 q = 0) : d154997 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152900, d154997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d152900, d154997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d152859 q = 0) : d154956 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152859, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d152859, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d152901 q = 0) : d154998 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d152901, d154998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d152901, d154998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d152902 q = 0) : d154999 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d152902, d154999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d152902, d154999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d290570 q = 0) : d292189 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290570, d292189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d290570, d292189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d290571 q = 0) : d292190 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d290571, d292190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d290571, d292190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro30583 (p : Pattern) (selected : d290577 p = 0) : d292196 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290572 q = 0) : d292191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290572, d292191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30582 q selected
    | true =>
      simp only [d290572, d292191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13757 q selected
  have h2 (q : Pattern) (selected : d290573 q = 0) : d292192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290573, d292192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290573, d292192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290574 q = 0) : d292193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290574, d292193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290574, d292193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153046 q = 0) : d155120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d153046, d155120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13757 q selected
    | true =>
      simp only [d153046, d155120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13732 q selected
  have h5 (q : Pattern) (selected : d153047 q = 0) : d155121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d153047, d155121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153047, d155121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153048 q = 0) : d155122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d153048, d155122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153048, d155122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290575 q = 0) : d292194 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290575, d292194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290575, d292194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d152905 q = 0) : d155002 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d152905, d155002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13732 q selected
    | true =>
      simp only [d152905, d155002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d152906 q = 0) : d155003 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d152906, d155003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152906, d155003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d152907 q = 0) : d155004 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d152907, d155004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152907, d155004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d153049 q = 0) : d155123 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d153049, d155123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d153049, d155123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d290576 q = 0) : d292195 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d290576, d292195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290576, d292195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d290577 q = 0) : d292196 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d290577, d292196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d290577, d292196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro30584 (p : Pattern) (selected : d290583 p = 0) : d292202 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290578 q = 0) : d292197 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290578, d292197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30583 q selected
    | true =>
      simp only [d290578, d292197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290579 q = 0) : d292198 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290579, d292198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290579, d292198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d153052 q = 0) : d155126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d153052, d155126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13758 q selected
    | true =>
      simp only [d153052, d155126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d153053 q = 0) : d155127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d153053, d155127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153053, d155127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290580 q = 0) : d292199 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290580, d292199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290580, d292199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290581 q = 0) : d292200 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290581, d292200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290581, d292200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290582 q = 0) : d292201 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290582, d292201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290582, d292201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290583 q = 0) : d292202 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290583, d292202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290583, d292202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30585 (p : Pattern) (selected : d290589 p = 0) : d292208 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290584 q = 0) : d292203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290584, d292203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30584 q selected
    | true =>
      simp only [d290584, d292203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13759 q selected
  have h2 (q : Pattern) (selected : d153261 q = 0) : d155132 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153261, d155132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13795 q selected
    | true =>
      simp only [d153261, d155132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13762 q selected
  have h3 (q : Pattern) (selected : d290585 q = 0) : d292204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290585, d292204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290585, d292204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153267 q = 0) : d155280 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153267, d155280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13796 q selected
    | true =>
      simp only [d153267, d155280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153268 q = 0) : d155281 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153268, d155281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153268, d155281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290586 q = 0) : d292205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290586, d292205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290586, d292205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290587 q = 0) : d292206 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290587, d292206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290587, d292206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290588 q = 0) : d292207 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290588, d292207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290588, d292207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d290589 q = 0) : d292208 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290589, d292208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290589, d292208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro30586 (p : Pattern) (selected : d290595 p = 0) : d292214 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153100 q = 0) : d155155 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153100, d155155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153100, d155155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13766 q selected
  have h2 (q : Pattern) (selected : d153101 q = 0) : d155156 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153101, d155156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153101, d155156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153107 q = 0) : d155162 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153107, d155162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13766 q selected
    | true =>
      simp only [d153107, d155162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13767 q selected
  have h4 (q : Pattern) (selected : d153108 q = 0) : d155163 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d153108, d155163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153108, d155163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153109 q = 0) : d155164 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d153109, d155164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153109, d155164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290549 q = 0) : d292168 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290549, d292168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30578 q selected
    | true =>
      simp only [d290549, d292168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30580 q selected
  have h7 (q : Pattern) (selected : d153205 q = 0) : d155237 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153205, d155237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13787 q selected
    | true =>
      simp only [d153205, d155237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13738 q selected
  have h8 (q : Pattern) (selected : d290550 q = 0) : d292169 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290550, d292169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290550, d292169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d290551 q = 0) : d292170 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290551, d292170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290551, d292170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d290552 q = 0) : d292171 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290552, d292171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290552, d292171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d290556 q = 0) : d292175 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290556, d292175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290556, d292175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30581 q selected
  have h12 (q : Pattern) (selected : d153214 q = 0) : d155246 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153214, d155246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153214, d155246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13789 q selected
  have h13 (q : Pattern) (selected : d290557 q = 0) : d292176 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290557, d292176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d290557, d292176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d290558 q = 0) : d292177 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290558, d292177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d290558, d292177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d290559 q = 0) : d292178 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290559, d292178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d290559, d292178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d290560 q = 0) : d292179 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290560, d292179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d290560, d292179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d290590 q = 0) : d292209 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290590, d292209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290590, d292209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30585 q selected
  have h18 (q : Pattern) (selected : d153279 q = 0) : d155292 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d153279, d155292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153279, d155292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13798 q selected
  have h19 (q : Pattern) (selected : d290591 q = 0) : d292210 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290591, d292210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d290591, d292210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d290592 q = 0) : d292211 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290592, d292211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d290592, d292211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d290593 q = 0) : d292212 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290593, d292212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d290593, d292212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d290594 q = 0) : d292213 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290594, d292213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d290594, d292213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d290595 q = 0) : d292214 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290595, d292214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d290595, d292214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro30587 (p : Pattern) (selected : d290601 p = 0) : d292220 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290596 q = 0) : d292215 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290596, d292215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290596, d292215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30586 q selected
  have h2 (q : Pattern) (selected : d290597 q = 0) : d292216 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290597, d292216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290597, d292216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290598 q = 0) : d292217 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290598, d292217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290598, d292217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290599 q = 0) : d292218 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290599, d292218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290599, d292218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290600 q = 0) : d292219 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290600, d292219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290600, d292219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290601 q = 0) : d292220 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290601, d292220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290601, d292220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30588 (p : Pattern) (selected : d290604 p = 0) : d292223 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290511 q = 0) : d292130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290511, d292130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30573 q selected
    | true =>
      simp only [d290511, d292130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290512 q = 0) : d292131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290512, d292131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290512, d292131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d290513 q = 0) : d292132 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290513, d292132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290513, d292132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290514 q = 0) : d292133 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290514, d292133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290514, d292133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290517 q = 0) : d292136 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290517, d292136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30574 q selected
    | true =>
      simp only [d290517, d292136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290518 q = 0) : d292137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290518, d292137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290518, d292137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290519 q = 0) : d292138 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290519, d292138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290519, d292138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290520 q = 0) : d292139 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290520, d292139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290520, d292139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290521 q = 0) : d292140 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290521, d292140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290521, d292140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290603 q = 0) : d292222 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290603, d292222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290603, d292222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d290604 q = 0) : d292223 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d290604, d292223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290604, d292223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30589 (p : Pattern) (selected : d290606 p = 0) : d292225 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152963 q = 0) : d155060 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152963, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13741 q selected
    | true =>
      simp only [d152963, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152964 q = 0) : d155061 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152964, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d152964, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d152965 q = 0) : d155062 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d152965, d155062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152965, d155062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152966 q = 0) : d155063 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d152966, d155063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152966, d155063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290605 q = 0) : d292224 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290605, d292224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290605, d292224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290606 q = 0) : d292225 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d290606, d292225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290606, d292225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30590 (p : Pattern) (selected : d290616 p = 0) : d292235 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290607 q = 0) : d292226 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290607, d292226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30588 q selected
    | true =>
      simp only [d290607, d292226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30589 q selected
  have h2 (q : Pattern) (selected : d290608 q = 0) : d292227 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290608, d292227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290608, d292227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290609 q = 0) : d292228 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290609, d292228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290609, d292228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290610 q = 0) : d292229 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290610, d292229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30589 q selected
    | true =>
      simp only [d290610, d292229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290611 q = 0) : d292230 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290611, d292230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290611, d292230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290612 q = 0) : d292231 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290612, d292231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290612, d292231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290613 q = 0) : d292232 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290613, d292232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290613, d292232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290614 q = 0) : d292233 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290614, d292233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290614, d292233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290615 q = 0) : d292234 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d290615, d292234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290615, d292234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290616 q = 0) : d292235 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d290616, d292235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290616, d292235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30591 (p : Pattern) (selected : d290620 p = 0) : d292239 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290610 q = 0) : d292229 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290610, d292229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30589 q selected
    | true =>
      simp only [d290610, d292229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290611 q = 0) : d292230 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290611, d292230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290611, d292230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290612 q = 0) : d292231 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290612, d292231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290612, d292231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290614 q = 0) : d292233 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290614, d292233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290614, d292233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290619 q = 0) : d292238 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d290619, d292238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290619, d292238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290620 q = 0) : d292239 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d290620, d292239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290620, d292239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30592 (p : Pattern) (selected : d290626 p = 0) : d292245 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290617 q = 0) : d292236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290617, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30590 q selected
    | true =>
      simp only [d290617, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290618 q = 0) : d292237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290618, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290618, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290621 q = 0) : d292240 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30591 q selected
    | true =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290622 q = 0) : d292241 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290623 q = 0) : d292242 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290623, d292242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290623, d292242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290624 q = 0) : d292243 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290624, d292243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290624, d292243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290625 q = 0) : d292244 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290625, d292244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290625, d292244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290626 q = 0) : d292245 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290626, d292245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290626, d292245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30593 (p : Pattern) (selected : d290630 p = 0) : d292249 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290621 q = 0) : d292240 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30591 q selected
    | true =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290622 q = 0) : d292241 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290627 q = 0) : d292246 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290627, d292246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290627, d292246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290628 q = 0) : d292247 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290628, d292247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290628, d292247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290629 q = 0) : d292248 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290629, d292248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290629, d292248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290630 q = 0) : d292249 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290630, d292249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290630, d292249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30594 (p : Pattern) (selected : d290636 p = 0) : d292255 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290631 q = 0) : d292250 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290631, d292250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30592 q selected
    | true =>
      simp only [d290631, d292250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30593 q selected
  have h2 (q : Pattern) (selected : d290632 q = 0) : d292251 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290632, d292251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290632, d292251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290633 q = 0) : d292252 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290633, d292252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290633, d292252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290634 q = 0) : d292253 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290634, d292253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290634, d292253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290635 q = 0) : d292254 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290635, d292254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290635, d292254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290636 q = 0) : d292255 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290636, d292255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290636, d292255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30595 (p : Pattern) (selected : d290639 p = 0) : d292258 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290617 q = 0) : d292236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290617, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30590 q selected
    | true =>
      simp only [d290617, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290618 q = 0) : d292237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290618, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290618, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290621 q = 0) : d292240 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30591 q selected
    | true =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290622 q = 0) : d292241 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290623 q = 0) : d292242 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290623, d292242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290623, d292242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290624 q = 0) : d292243 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290624, d292243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290624, d292243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290625 q = 0) : d292244 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290625, d292244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290625, d292244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290639 q = 0) : d292258 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290639, d292258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290639, d292258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30596 (p : Pattern) (selected : d290640 p = 0) : d292259 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290621 q = 0) : d292240 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30591 q selected
    | true =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290622 q = 0) : d292241 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290627 q = 0) : d292246 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290627, d292246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290627, d292246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290628 q = 0) : d292247 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290628, d292247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290628, d292247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290629 q = 0) : d292248 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290629, d292248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290629, d292248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290640 q = 0) : d292259 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290640, d292259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290640, d292259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30597 (p : Pattern) (selected : d290646 p = 0) : d292265 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290631 q = 0) : d292250 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290631, d292250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30592 q selected
    | true =>
      simp only [d290631, d292250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30593 q selected
  have h2 (q : Pattern) (selected : d290632 q = 0) : d292251 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290632, d292251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290632, d292251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290633 q = 0) : d292252 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290633, d292252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290633, d292252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290634 q = 0) : d292253 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290634, d292253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290634, d292253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290635 q = 0) : d292254 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290635, d292254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290635, d292254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290641 q = 0) : d292260 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290641, d292260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30595 q selected
    | true =>
      simp only [d290641, d292260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30596 q selected
  have h7 (q : Pattern) (selected : d290642 q = 0) : d292261 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290642, d292261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290642, d292261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290643 q = 0) : d292262 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290643, d292262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290643, d292262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290644 q = 0) : d292263 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290644, d292263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290644, d292263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290645 q = 0) : d292264 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290645, d292264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290645, d292264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d290646 q = 0) : d292265 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290646, d292265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290646, d292265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30598 (p : Pattern) (selected : d290651 p = 0) : d292270 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290617 q = 0) : d292236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290617, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30590 q selected
    | true =>
      simp only [d290617, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290618 q = 0) : d292237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290618, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290618, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290621 q = 0) : d292240 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30591 q selected
    | true =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290622 q = 0) : d292241 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290623 q = 0) : d292242 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290623, d292242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290623, d292242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290624 q = 0) : d292243 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290624, d292243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290624, d292243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290650 q = 0) : d292269 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290650, d292269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290650, d292269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290651 q = 0) : d292270 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290651, d292270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290651, d292270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30599 (p : Pattern) (selected : d290653 p = 0) : d292272 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290621 q = 0) : d292240 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30591 q selected
    | true =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290622 q = 0) : d292241 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290627 q = 0) : d292246 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290627, d292246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290627, d292246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290628 q = 0) : d292247 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290628, d292247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290628, d292247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290652 q = 0) : d292271 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290652, d292271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290652, d292271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290653 q = 0) : d292272 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290653, d292272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290653, d292272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30600 (p : Pattern) (selected : d290660 p = 0) : d292279 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290617 q = 0) : d292236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290617, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30590 q selected
    | true =>
      simp only [d290617, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290618 q = 0) : d292237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290618, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290618, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290621 q = 0) : d292240 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30591 q selected
    | true =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290622 q = 0) : d292241 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290623 q = 0) : d292242 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290623, d292242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290623, d292242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290658 q = 0) : d292277 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290658, d292277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290658, d292277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290659 q = 0) : d292278 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290659, d292278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290659, d292278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290660 q = 0) : d292279 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290660, d292279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290660, d292279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30601 (p : Pattern) (selected : d290663 p = 0) : d292282 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290621 q = 0) : d292240 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30591 q selected
    | true =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290622 q = 0) : d292241 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290627 q = 0) : d292246 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290627, d292246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290627, d292246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290661 q = 0) : d292280 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290661, d292280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290661, d292280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290662 q = 0) : d292281 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290662, d292281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290662, d292281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290663 q = 0) : d292282 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290663, d292282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290663, d292282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30602 (p : Pattern) (selected : d290668 p = 0) : d292287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d531 q = 0) : d52278 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d52278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro275 q selected
    | true =>
      simp only [d531, d52278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d532 q = 0) : d52279 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d52279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d532, d52279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d25765 q = 0) : d199013 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25765, d199013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18806 q selected
    | true =>
      simp only [d25765, d199013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25766 q = 0) : d199014 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25766, d199014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25766, d199014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290667 q = 0) : d292286 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d290667, d292286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290667, d292286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290668 q = 0) : d292287 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d290668, d292287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290668, d292287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30603 (p : Pattern) (selected : d290674 p = 0) : d292293 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d313 q = 0) : d52112 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro234 q selected
    | true =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314 q = 0) : d52113 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d290673 q = 0) : d292292 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d290673, d292292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290673, d292292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290674 q = 0) : d292293 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d290674, d292293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290674, d292293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro30604 (p : Pattern) (selected : d290681 p = 0) : d292300 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290669 q = 0) : d292288 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290669, d292288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30602 q selected
    | true =>
      simp only [d290669, d292288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290670 q = 0) : d292289 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290670, d292289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290670, d292289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d290671 q = 0) : d292290 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290671, d292290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290671, d292290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290672 q = 0) : d292291 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290672, d292291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290672, d292291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290675 q = 0) : d292294 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290675, d292294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30603 q selected
    | true =>
      simp only [d290675, d292294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290676 q = 0) : d292295 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290676, d292295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290676, d292295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290677 q = 0) : d292296 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290677, d292296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290677, d292296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290678 q = 0) : d292297 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290678, d292297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290678, d292297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290679 q = 0) : d292298 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290679, d292298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290679, d292298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290517 q = 0) : d292136 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290517, d292136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30574 q selected
    | true =>
      simp only [d290517, d292136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d290518 q = 0) : d292137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290518, d292137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d290518, d292137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d290519 q = 0) : d292138 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290519, d292138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290519, d292138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d290520 q = 0) : d292139 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290520, d292139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d290520, d292139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d290680 q = 0) : d292299 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290680, d292299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290680, d292299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d290681 q = 0) : d292300 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d290681, d292300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290681, d292300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30605 (p : Pattern) (selected : d290685 p = 0) : d292304 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290517 q = 0) : d292136 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290517, d292136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30574 q selected
    | true =>
      simp only [d290517, d292136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290518 q = 0) : d292137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290518, d292137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290518, d292137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d290519 q = 0) : d292138 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290519, d292138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290519, d292138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290520 q = 0) : d292139 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290520, d292139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290520, d292139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290603 q = 0) : d292222 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290603, d292222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290603, d292222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290685 q = 0) : d292304 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d290685, d292304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290685, d292304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30606 (p : Pattern) (selected : d290691 p = 0) : d292310 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290682 q = 0) : d292301 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290682, d292301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30604 q selected
    | true =>
      simp only [d290682, d292301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30588 q selected
  have h2 (q : Pattern) (selected : d290683 q = 0) : d292302 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290683, d292302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290683, d292302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290684 q = 0) : d292303 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290684, d292303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290684, d292303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290686 q = 0) : d292305 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290686, d292305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30588 q selected
    | true =>
      simp only [d290686, d292305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30605 q selected
  have h5 (q : Pattern) (selected : d290687 q = 0) : d292306 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290687, d292306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290687, d292306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290688 q = 0) : d292307 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290688, d292307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290688, d292307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290689 q = 0) : d292308 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290689, d292308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290689, d292308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290607 q = 0) : d292226 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290607, d292226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30588 q selected
    | true =>
      simp only [d290607, d292226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30589 q selected
  have h9 (q : Pattern) (selected : d290608 q = 0) : d292227 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290608, d292227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290608, d292227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290609 q = 0) : d292228 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290609, d292228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290609, d292228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d290610 q = 0) : d292229 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290610, d292229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30589 q selected
    | true =>
      simp only [d290610, d292229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d290611 q = 0) : d292230 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290611, d292230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290611, d292230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d290612 q = 0) : d292231 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290612, d292231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290612, d292231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d290613 q = 0) : d292232 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290613, d292232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d290613, d292232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d290690 q = 0) : d292309 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d290690, d292309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290690, d292309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d290691 q = 0) : d292310 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d290691, d292310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d290691, d292310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro30607 (p : Pattern) (selected : d290697 p = 0) : d292316 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290692 q = 0) : d292311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290692, d292311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30606 q selected
    | true =>
      simp only [d290692, d292311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290693 q = 0) : d292312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290693, d292312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290693, d292312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290617 q = 0) : d292236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290617, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30590 q selected
    | true =>
      simp only [d290617, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290618 q = 0) : d292237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290618, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290618, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290694 q = 0) : d292313 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290694, d292313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290694, d292313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290695 q = 0) : d292314 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290695, d292314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290695, d292314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290696 q = 0) : d292315 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290696, d292315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290696, d292315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290697 q = 0) : d292316 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290697, d292316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290697, d292316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30608 (p : Pattern) (selected : d290700 p = 0) : d292129 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d568 q = 0) : d52112 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d568, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro281 q selected
    | true =>
      simp only [d568, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d569 q = 0) : d52113 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d569, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d569, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d25812 q = 0) : d198756 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25812, d198756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18814 q selected
    | true =>
      simp only [d25812, d198756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25813 q = 0) : d198757 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25813, d198757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25813, d198757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290699 q = 0) : d292128 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d290699, d292128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290699, d292128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290700 q = 0) : d292129 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d290700, d292129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290700, d292129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30609 (p : Pattern) (selected : d290706 p = 0) : d292135 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d344 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro239 q selected
    | true =>
      simp only [d344, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d290705 q = 0) : d292134 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d290705, d292134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290705, d292134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290706 q = 0) : d292135 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d290706, d292135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290706, d292135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro30610 (p : Pattern) (selected : d290713 p = 0) : d292223 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290701 q = 0) : d292130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290701, d292130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30608 q selected
    | true =>
      simp only [d290701, d292130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290702 q = 0) : d292131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290702, d292131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290702, d292131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d290703 q = 0) : d292132 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290703, d292132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290703, d292132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290704 q = 0) : d292133 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290704, d292133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290704, d292133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290707 q = 0) : d292136 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290707, d292136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30609 q selected
    | true =>
      simp only [d290707, d292136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290708 q = 0) : d292137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290708, d292137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290708, d292137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290709 q = 0) : d292138 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290709, d292138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290709, d292138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290710 q = 0) : d292139 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290710, d292139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290710, d292139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290711 q = 0) : d292140 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290711, d292140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290711, d292140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290712 q = 0) : d292222 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290712, d292222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290712, d292222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d290713 q = 0) : d292223 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d290713, d292223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290713, d292223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30611 (p : Pattern) (selected : d290715 p = 0) : d292225 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153152 q = 0) : d155060 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153152, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13775 q selected
    | true =>
      simp only [d153152, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153153 q = 0) : d155061 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153153, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153153, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153154 q = 0) : d155062 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153154, d155062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153154, d155062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153155 q = 0) : d155063 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153155, d155063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153155, d155063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290714 q = 0) : d292224 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290714, d292224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290714, d292224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290715 q = 0) : d292225 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d290715, d292225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290715, d292225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30612 (p : Pattern) (selected : d290725 p = 0) : d292235 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290716 q = 0) : d292226 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290716, d292226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30610 q selected
    | true =>
      simp only [d290716, d292226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30611 q selected
  have h2 (q : Pattern) (selected : d290717 q = 0) : d292227 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290717, d292227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290717, d292227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290718 q = 0) : d292228 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290718, d292228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290718, d292228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290719 q = 0) : d292229 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290719, d292229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30611 q selected
    | true =>
      simp only [d290719, d292229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290720 q = 0) : d292230 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290720, d292230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290720, d292230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290721 q = 0) : d292231 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290721, d292231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290721, d292231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290722 q = 0) : d292232 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290722, d292232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290722, d292232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290723 q = 0) : d292233 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290723, d292233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290723, d292233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290724 q = 0) : d292234 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d290724, d292234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290724, d292234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290725 q = 0) : d292235 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d290725, d292235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290725, d292235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30613 (p : Pattern) (selected : d290729 p = 0) : d292239 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290719 q = 0) : d292229 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290719, d292229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30611 q selected
    | true =>
      simp only [d290719, d292229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290720 q = 0) : d292230 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290720, d292230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290720, d292230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290721 q = 0) : d292231 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290721, d292231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290721, d292231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290723 q = 0) : d292233 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290723, d292233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290723, d292233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290728 q = 0) : d292238 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d290728, d292238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290728, d292238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290729 q = 0) : d292239 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d290729, d292239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290729, d292239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30614 (p : Pattern) (selected : d290735 p = 0) : d292245 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290726 q = 0) : d292236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290726, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30612 q selected
    | true =>
      simp only [d290726, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290727 q = 0) : d292237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290727, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290727, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290730 q = 0) : d292240 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290730, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30613 q selected
    | true =>
      simp only [d290730, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290731 q = 0) : d292241 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290731, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290731, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290732 q = 0) : d292242 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290732, d292242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290732, d292242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290733 q = 0) : d292243 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290733, d292243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290733, d292243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290734 q = 0) : d292244 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290734, d292244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290734, d292244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290735 q = 0) : d292245 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290735, d292245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290735, d292245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30615 (p : Pattern) (selected : d290739 p = 0) : d292249 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290730 q = 0) : d292240 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290730, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30613 q selected
    | true =>
      simp only [d290730, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290731 q = 0) : d292241 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290731, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290731, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290736 q = 0) : d292246 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290736, d292246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290736, d292246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290737 q = 0) : d292247 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290737, d292247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290737, d292247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290738 q = 0) : d292248 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290738, d292248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290738, d292248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290739 q = 0) : d292249 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290739, d292249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290739, d292249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30616 (p : Pattern) (selected : d290745 p = 0) : d292322 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290617 q = 0) : d292236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290617, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30590 q selected
    | true =>
      simp only [d290617, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290618 q = 0) : d292237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290618, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290618, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290742 q = 0) : d292319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290742, d292319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290742, d292319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290743 q = 0) : d292320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290743, d292320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290743, d292320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290744 q = 0) : d292321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290744, d292321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290744, d292321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290745 q = 0) : d292322 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290745, d292322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290745, d292322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30617 (p : Pattern) (selected : d290751 p = 0) : d292328 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290654 q = 0) : d292273 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290654, d292273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30598 q selected
    | true =>
      simp only [d290654, d292273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30599 q selected
  have h2 (q : Pattern) (selected : d290655 q = 0) : d292274 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290655, d292274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290655, d292274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290656 q = 0) : d292275 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290656, d292275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290656, d292275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290657 q = 0) : d292276 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290657, d292276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290657, d292276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290664 q = 0) : d292283 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290664, d292283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30600 q selected
    | true =>
      simp only [d290664, d292283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30601 q selected
  have h6 (q : Pattern) (selected : d290665 q = 0) : d292284 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290665, d292284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290665, d292284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290666 q = 0) : d292285 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290666, d292285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290666, d292285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290698 q = 0) : d292317 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290698, d292317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30607 q selected
    | true =>
      simp only [d290698, d292317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30592 q selected
  have h9 (q : Pattern) (selected : d290740 q = 0) : d292250 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290740, d292250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30614 q selected
    | true =>
      simp only [d290740, d292250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30615 q selected
  have h10 (q : Pattern) (selected : d290741 q = 0) : d292318 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290741, d292318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290741, d292318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d290746 q = 0) : d292323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290746, d292323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30616 q selected
    | true =>
      simp only [d290746, d292323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d290747 q = 0) : d292324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290747, d292324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d290747, d292324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d290748 q = 0) : d292325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290748, d292325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d290748, d292325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d290749 q = 0) : d292326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290749, d292326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290749, d292326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d290750 q = 0) : d292327 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290750, d292327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290750, d292327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d290751 q = 0) : d292328 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290751, d292328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290751, d292328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro30618 (p : Pattern) (selected : d290752 p = 0) : d292329 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290617 q = 0) : d292236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290617, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30590 q selected
    | true =>
      simp only [d290617, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290618 q = 0) : d292237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290618, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290618, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290621 q = 0) : d292240 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30591 q selected
    | true =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290622 q = 0) : d292241 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290623 q = 0) : d292242 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290623, d292242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290623, d292242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290624 q = 0) : d292243 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290624, d292243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290624, d292243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290650 q = 0) : d292269 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290650, d292269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290650, d292269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290752 q = 0) : d292329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290752, d292329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290752, d292329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30619 (p : Pattern) (selected : d290753 p = 0) : d292330 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290621 q = 0) : d292240 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30591 q selected
    | true =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290622 q = 0) : d292241 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290627 q = 0) : d292246 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290627, d292246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290627, d292246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290628 q = 0) : d292247 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290628, d292247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290628, d292247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290652 q = 0) : d292271 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290652, d292271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290652, d292271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290753 q = 0) : d292330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290753, d292330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290753, d292330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30620 (p : Pattern) (selected : d290758 p = 0) : d292335 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290617 q = 0) : d292236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290617, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30590 q selected
    | true =>
      simp only [d290617, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290618 q = 0) : d292237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290618, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290618, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290621 q = 0) : d292240 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30591 q selected
    | true =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290622 q = 0) : d292241 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290623 q = 0) : d292242 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290623, d292242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290623, d292242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290658 q = 0) : d292277 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290658, d292277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290658, d292277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290659 q = 0) : d292278 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290659, d292278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290659, d292278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290758 q = 0) : d292335 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290758, d292335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290758, d292335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30621 (p : Pattern) (selected : d290759 p = 0) : d292336 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290621 q = 0) : d292240 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30591 q selected
    | true =>
      simp only [d290621, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290622 q = 0) : d292241 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290622, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290627 q = 0) : d292246 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290627, d292246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290627, d292246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290661 q = 0) : d292280 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290661, d292280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290661, d292280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290662 q = 0) : d292281 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290662, d292281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290662, d292281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290759 q = 0) : d292336 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290759, d292336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290759, d292336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30622 (p : Pattern) (selected : d290763 p = 0) : d292340 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290692 q = 0) : d292311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290692, d292311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30606 q selected
    | true =>
      simp only [d290692, d292311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290693 q = 0) : d292312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290693, d292312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290693, d292312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290617 q = 0) : d292236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290617, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30590 q selected
    | true =>
      simp only [d290617, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290618 q = 0) : d292237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290618, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290618, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290694 q = 0) : d292313 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290694, d292313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290694, d292313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290695 q = 0) : d292314 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290695, d292314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290695, d292314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290696 q = 0) : d292315 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290696, d292315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290696, d292315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290763 q = 0) : d292340 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290763, d292340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290763, d292340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30623 (p : Pattern) (selected : d290765 p = 0) : d292258 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290726 q = 0) : d292236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290726, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30612 q selected
    | true =>
      simp only [d290726, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290727 q = 0) : d292237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290727, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290727, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290730 q = 0) : d292240 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290730, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30613 q selected
    | true =>
      simp only [d290730, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290731 q = 0) : d292241 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290731, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290731, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290732 q = 0) : d292242 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290732, d292242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290732, d292242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290733 q = 0) : d292243 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290733, d292243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290733, d292243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290734 q = 0) : d292244 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290734, d292244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290734, d292244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290765 q = 0) : d292258 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290765, d292258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290765, d292258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30624 (p : Pattern) (selected : d290766 p = 0) : d292259 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290730 q = 0) : d292240 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290730, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30613 q selected
    | true =>
      simp only [d290730, d292240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290731 q = 0) : d292241 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290731, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290731, d292241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290736 q = 0) : d292246 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290736, d292246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290736, d292246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290737 q = 0) : d292247 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290737, d292247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290737, d292247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290738 q = 0) : d292248 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290738, d292248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290738, d292248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290766 q = 0) : d292259 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290766, d292259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290766, d292259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30625 (p : Pattern) (selected : d290769 p = 0) : d292343 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290617 q = 0) : d292236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290617, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30590 q selected
    | true =>
      simp only [d290617, d292236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290618 q = 0) : d292237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290618, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290618, d292237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290742 q = 0) : d292319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290742, d292319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290742, d292319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290743 q = 0) : d292320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290743, d292320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290743, d292320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290744 q = 0) : d292321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290744, d292321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290744, d292321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290769 q = 0) : d292343 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290769, d292343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290769, d292343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30626 (p : Pattern) (selected : d290775 p = 0) : d292349 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290654 q = 0) : d292273 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290654, d292273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30598 q selected
    | true =>
      simp only [d290654, d292273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30599 q selected
  have h2 (q : Pattern) (selected : d290655 q = 0) : d292274 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290655, d292274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290655, d292274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290656 q = 0) : d292275 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290656, d292275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290656, d292275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290657 q = 0) : d292276 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290657, d292276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290657, d292276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290664 q = 0) : d292283 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290664, d292283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30600 q selected
    | true =>
      simp only [d290664, d292283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30601 q selected
  have h6 (q : Pattern) (selected : d290665 q = 0) : d292284 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290665, d292284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290665, d292284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290666 q = 0) : d292285 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290666, d292285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290666, d292285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290698 q = 0) : d292317 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290698, d292317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30607 q selected
    | true =>
      simp only [d290698, d292317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30592 q selected
  have h9 (q : Pattern) (selected : d290740 q = 0) : d292250 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290740, d292250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30614 q selected
    | true =>
      simp only [d290740, d292250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30615 q selected
  have h10 (q : Pattern) (selected : d290741 q = 0) : d292318 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290741, d292318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290741, d292318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d290746 q = 0) : d292323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290746, d292323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30616 q selected
    | true =>
      simp only [d290746, d292323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d290747 q = 0) : d292324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290747, d292324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d290747, d292324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d290748 q = 0) : d292325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290748, d292325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d290748, d292325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d290749 q = 0) : d292326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290749, d292326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290749, d292326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d290750 q = 0) : d292327 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290750, d292327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290750, d292327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d290754 q = 0) : d292331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290754, d292331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30618 q selected
    | true =>
      simp only [d290754, d292331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30619 q selected
  have h17 (q : Pattern) (selected : d290755 q = 0) : d292332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290755, d292332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290755, d292332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d290756 q = 0) : d292333 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290756, d292333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d290756, d292333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d290757 q = 0) : d292334 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290757, d292334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290757, d292334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d290760 q = 0) : d292337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290760, d292337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30620 q selected
    | true =>
      simp only [d290760, d292337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30621 q selected
  have h21 (q : Pattern) (selected : d290761 q = 0) : d292338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290761, d292338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290761, d292338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d290762 q = 0) : d292339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290762, d292339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d290762, d292339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d290764 q = 0) : d292341 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290764, d292341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30622 q selected
    | true =>
      simp only [d290764, d292341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30595 q selected
  have h24 (q : Pattern) (selected : d290767 q = 0) : d292260 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290767, d292260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30623 q selected
    | true =>
      simp only [d290767, d292260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30624 q selected
  have h25 (q : Pattern) (selected : d290768 q = 0) : d292342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290768, d292342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d290768, d292342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d290770 q = 0) : d292344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290770, d292344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30625 q selected
    | true =>
      simp only [d290770, d292344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d290771 q = 0) : d292345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290771, d292345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d290771, d292345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d290772 q = 0) : d292346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290772, d292346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d290772, d292346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d290773 q = 0) : d292347 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290773, d292347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d290773, d292347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d290774 q = 0) : d292348 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290774, d292348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d290774, d292348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d290775 q = 0) : d292349 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290775, d292349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d290775, d292349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro30627 (p : Pattern) (selected : d290782 p = 0) : d292356 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290631 q = 0) : d292250 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290631, d292250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30592 q selected
    | true =>
      simp only [d290631, d292250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30593 q selected
  have h2 (q : Pattern) (selected : d290632 q = 0) : d292251 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290632, d292251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290632, d292251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290633 q = 0) : d292252 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290633, d292252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290633, d292252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290634 q = 0) : d292253 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290634, d292253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290634, d292253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290635 q = 0) : d292254 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290635, d292254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290635, d292254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290777 q = 0) : d292351 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290777, d292351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30593 q selected
    | true =>
      simp only [d290777, d292351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290778 q = 0) : d292352 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290778, d292352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290778, d292352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290779 q = 0) : d292353 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290779, d292353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290779, d292353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290780 q = 0) : d292354 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290780, d292354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290780, d292354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290781 q = 0) : d292355 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290781, d292355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290781, d292355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d290782 q = 0) : d292356 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290782, d292356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290782, d292356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30628 (p : Pattern) (selected : d290788 p = 0) : d292362 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290777 q = 0) : d292351 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290777, d292351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30593 q selected
    | true =>
      simp only [d290777, d292351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290778 q = 0) : d292352 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290778, d292352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290778, d292352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290779 q = 0) : d292353 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290779, d292353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290779, d292353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290780 q = 0) : d292354 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290780, d292354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290780, d292354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290781 q = 0) : d292355 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290781, d292355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290781, d292355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290783 q = 0) : d292357 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290783, d292357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30596 q selected
    | true =>
      simp only [d290783, d292357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290784 q = 0) : d292358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290784, d292358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290784, d292358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290785 q = 0) : d292359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290785, d292359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290785, d292359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290786 q = 0) : d292360 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290786, d292360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290786, d292360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290787 q = 0) : d292361 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290787, d292361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290787, d292361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d290788 q = 0) : d292362 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290788, d292362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290788, d292362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30629 (p : Pattern) (selected : d290795 p = 0) : d292369 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290764 q = 0) : d292341 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290764, d292341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30622 q selected
    | true =>
      simp only [d290764, d292341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30595 q selected
  have h2 (q : Pattern) (selected : d290767 q = 0) : d292260 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290767, d292260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30623 q selected
    | true =>
      simp only [d290767, d292260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30624 q selected
  have h3 (q : Pattern) (selected : d290768 q = 0) : d292342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290768, d292342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290768, d292342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290770 q = 0) : d292344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290770, d292344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30625 q selected
    | true =>
      simp only [d290770, d292344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290771 q = 0) : d292345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290771, d292345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290771, d292345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290772 q = 0) : d292346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290772, d292346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290772, d292346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290793 q = 0) : d292367 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290793, d292367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290793, d292367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290794 q = 0) : d292368 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290794, d292368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290794, d292368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d290795 q = 0) : d292369 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290795, d292369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290795, d292369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro30630 (p : Pattern) (selected : d290797 p = 0) : d292371 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290783 q = 0) : d292357 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290783, d292357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30596 q selected
    | true =>
      simp only [d290783, d292357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290784 q = 0) : d292358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290784, d292358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290784, d292358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290785 q = 0) : d292359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290785, d292359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290785, d292359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290786 q = 0) : d292360 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290786, d292360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290786, d292360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290787 q = 0) : d292361 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290787, d292361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290787, d292361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290797 q = 0) : d292371 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290797, d292371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290797, d292371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30631 (p : Pattern) (selected : d290813 p = 0) : d292387 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290803 q = 0) : d292377 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290803, d292377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290803, d292377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30602 q selected
  have h2 (q : Pattern) (selected : d290669 q = 0) : d292288 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290669, d292288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30602 q selected
    | true =>
      simp only [d290669, d292288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d290804 q = 0) : d292378 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290804, d292378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290804, d292378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290670 q = 0) : d292289 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290670, d292289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290670, d292289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290805 q = 0) : d292379 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290805, d292379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290805, d292379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290806 q = 0) : d292380 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290806, d292380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290806, d292380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290807 q = 0) : d292381 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290807, d292381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290807, d292381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30603 q selected
  have h8 (q : Pattern) (selected : d290675 q = 0) : d292294 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290675, d292294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30603 q selected
    | true =>
      simp only [d290675, d292294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290808 q = 0) : d292382 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290808, d292382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290808, d292382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290676 q = 0) : d292295 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290676, d292295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290676, d292295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d290809 q = 0) : d292383 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290809, d292383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290809, d292383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d290810 q = 0) : d292384 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290810, d292384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d290810, d292384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d290811 q = 0) : d292385 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290811, d292385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290811, d292385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d290565 q = 0) : d292184 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290565, d292184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290565, d292184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30574 q selected
  have h15 (q : Pattern) (selected : d290517 q = 0) : d292136 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290517, d292136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30574 q selected
    | true =>
      simp only [d290517, d292136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d290566 q = 0) : d292185 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290566, d292185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d290566, d292185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d290518 q = 0) : d292137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290518, d292137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d290518, d292137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d290567 q = 0) : d292186 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290567, d292186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d290567, d292186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d290568 q = 0) : d292187 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290568, d292187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d290568, d292187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d290812 q = 0) : d292386 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290812, d292386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d290812, d292386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d290813 q = 0) : d292387 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d290813, d292387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d290813, d292387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro30632 (p : Pattern) (selected : d290815 p = 0) : d292389 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290561 q = 0) : d292180 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290561, d292180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290561, d292180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30573 q selected
  have h2 (q : Pattern) (selected : d290511 q = 0) : d292130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290511, d292130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30573 q selected
    | true =>
      simp only [d290511, d292130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d290562 q = 0) : d292181 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290562, d292181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290562, d292181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290512 q = 0) : d292131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290512, d292131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290512, d292131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290563 q = 0) : d292182 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290563, d292182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290563, d292182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290564 q = 0) : d292183 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290564, d292183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290564, d292183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290565 q = 0) : d292184 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290565, d292184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290565, d292184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30574 q selected
  have h8 (q : Pattern) (selected : d290517 q = 0) : d292136 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290517, d292136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30574 q selected
    | true =>
      simp only [d290517, d292136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290566 q = 0) : d292185 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290566, d292185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290566, d292185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290518 q = 0) : d292137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290518, d292137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290518, d292137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d290567 q = 0) : d292186 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290567, d292186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290567, d292186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d290568 q = 0) : d292187 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290568, d292187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d290568, d292187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d290569 q = 0) : d292188 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290569, d292188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290569, d292188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d290814 q = 0) : d292388 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290814, d292388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d290814, d292388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d290815 q = 0) : d292389 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d290815, d292389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d290815, d292389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30633 (p : Pattern) (selected : d290819 p = 0) : d292393 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290565 q = 0) : d292184 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290565, d292184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290565, d292184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30574 q selected
  have h2 (q : Pattern) (selected : d290517 q = 0) : d292136 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290517, d292136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30574 q selected
    | true =>
      simp only [d290517, d292136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d290566 q = 0) : d292185 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290566, d292185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290566, d292185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290518 q = 0) : d292137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290518, d292137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290518, d292137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290567 q = 0) : d292186 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290567, d292186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290567, d292186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290568 q = 0) : d292187 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290568, d292187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290568, d292187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290814 q = 0) : d292388 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290814, d292388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290814, d292388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290819 q = 0) : d292393 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d290819, d292393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290819, d292393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30634 (p : Pattern) (selected : d290825 p = 0) : d292399 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153040 q = 0) : d155114 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153040, d155114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153040, d155114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13741 q selected
  have h2 (q : Pattern) (selected : d152963 q = 0) : d155060 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152963, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13741 q selected
    | true =>
      simp only [d152963, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153041 q = 0) : d155115 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153041, d155115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153041, d155115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152964 q = 0) : d155061 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152964, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152964, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153042 q = 0) : d155116 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153042, d155116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153042, d155116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153043 q = 0) : d155117 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153043, d155117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153043, d155117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290824 q = 0) : d292398 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290824, d292398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290824, d292398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290825 q = 0) : d292399 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d290825, d292399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290825, d292399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30635 (p : Pattern) (selected : d290834 p = 0) : d292408 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290816 q = 0) : d292390 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290816, d292390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30631 q selected
    | true =>
      simp only [d290816, d292390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30632 q selected
  have h2 (q : Pattern) (selected : d290817 q = 0) : d292391 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290817, d292391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290817, d292391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290818 q = 0) : d292392 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290818, d292392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290818, d292392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290820 q = 0) : d292394 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290820, d292394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30632 q selected
    | true =>
      simp only [d290820, d292394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30633 q selected
  have h5 (q : Pattern) (selected : d290821 q = 0) : d292395 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290821, d292395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290821, d292395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290822 q = 0) : d292396 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290822, d292396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290822, d292396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290823 q = 0) : d292397 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290823, d292397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290823, d292397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290826 q = 0) : d292400 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290826, d292400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30632 q selected
    | true =>
      simp only [d290826, d292400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30634 q selected
  have h9 (q : Pattern) (selected : d290827 q = 0) : d292401 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290827, d292401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290827, d292401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290828 q = 0) : d292402 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290828, d292402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290828, d292402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d290829 q = 0) : d292403 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290829, d292403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30634 q selected
    | true =>
      simp only [d290829, d292403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d290830 q = 0) : d292404 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290830, d292404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290830, d292404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d290831 q = 0) : d292405 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290831, d292405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290831, d292405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d290832 q = 0) : d292406 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290832, d292406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d290832, d292406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d290833 q = 0) : d292407 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d290833, d292407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290833, d292407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d290834 q = 0) : d292408 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d290834, d292408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d290834, d292408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro30636 (p : Pattern) (selected : d290839 p = 0) : d292413 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290826 q = 0) : d292400 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290826, d292400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30632 q selected
    | true =>
      simp only [d290826, d292400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30634 q selected
  have h2 (q : Pattern) (selected : d290827 q = 0) : d292401 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290827, d292401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290827, d292401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290828 q = 0) : d292402 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290828, d292402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290828, d292402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290829 q = 0) : d292403 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290829, d292403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30634 q selected
    | true =>
      simp only [d290829, d292403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290830 q = 0) : d292404 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290830, d292404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290830, d292404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290831 q = 0) : d292405 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290831, d292405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290831, d292405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290832 q = 0) : d292406 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290832, d292406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290832, d292406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290837 q = 0) : d292411 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290837, d292411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290837, d292411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290838 q = 0) : d292412 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d290838, d292412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290838, d292412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290839 q = 0) : d292413 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d290839, d292413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290839, d292413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30637 (p : Pattern) (selected : d290845 p = 0) : d292419 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290835 q = 0) : d292409 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290835, d292409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30635 q selected
    | true =>
      simp only [d290835, d292409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290836 q = 0) : d292410 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290836, d292410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290836, d292410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290840 q = 0) : d292414 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290840, d292414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30636 q selected
    | true =>
      simp only [d290840, d292414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290841 q = 0) : d292415 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290841, d292415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290841, d292415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290842 q = 0) : d292416 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290842, d292416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290842, d292416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290843 q = 0) : d292417 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290843, d292417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290843, d292417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290844 q = 0) : d292418 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290844, d292418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290844, d292418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290845 q = 0) : d292419 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290845, d292419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290845, d292419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30638 (p : Pattern) (selected : d290847 p = 0) : d292421 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290829 q = 0) : d292403 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290829, d292403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30634 q selected
    | true =>
      simp only [d290829, d292403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290830 q = 0) : d292404 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290830, d292404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290830, d292404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290831 q = 0) : d292405 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290831, d292405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290831, d292405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290837 q = 0) : d292411 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290837, d292411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290837, d292411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290846 q = 0) : d292420 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d290846, d292420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290846, d292420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290847 q = 0) : d292421 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d290847, d292421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290847, d292421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30639 (p : Pattern) (selected : d290853 p = 0) : d292427 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290840 q = 0) : d292414 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290840, d292414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30636 q selected
    | true =>
      simp only [d290840, d292414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290841 q = 0) : d292415 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290841, d292415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290841, d292415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290848 q = 0) : d292422 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290848, d292422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30638 q selected
    | true =>
      simp only [d290848, d292422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290849 q = 0) : d292423 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290849, d292423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290849, d292423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290850 q = 0) : d292424 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290850, d292424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290850, d292424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290851 q = 0) : d292425 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290851, d292425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290851, d292425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290852 q = 0) : d292426 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290852, d292426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290852, d292426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290853 q = 0) : d292427 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290853, d292427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290853, d292427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30640 (p : Pattern) (selected : d290865 p = 0) : d292389 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290855 q = 0) : d292180 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290855, d292180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290855, d292180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30608 q selected
  have h2 (q : Pattern) (selected : d290701 q = 0) : d292130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290701, d292130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30608 q selected
    | true =>
      simp only [d290701, d292130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d290856 q = 0) : d292181 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290856, d292181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290856, d292181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290702 q = 0) : d292131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290702, d292131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290702, d292131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290857 q = 0) : d292182 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290857, d292182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290857, d292182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290858 q = 0) : d292183 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290858, d292183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290858, d292183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290859 q = 0) : d292184 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290859, d292184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290859, d292184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30609 q selected
  have h8 (q : Pattern) (selected : d290707 q = 0) : d292136 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290707, d292136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30609 q selected
    | true =>
      simp only [d290707, d292136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290860 q = 0) : d292185 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290860, d292185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290860, d292185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290708 q = 0) : d292137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290708, d292137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290708, d292137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d290861 q = 0) : d292186 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290861, d292186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290861, d292186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d290862 q = 0) : d292187 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290862, d292187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d290862, d292187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d290863 q = 0) : d292188 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290863, d292188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290863, d292188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d290864 q = 0) : d292388 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290864, d292388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d290864, d292388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d290865 q = 0) : d292389 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d290865, d292389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d290865, d292389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30641 (p : Pattern) (selected : d290867 p = 0) : d292399 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d153243 q = 0) : d155114 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153243, d155114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153243, d155114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13775 q selected
  have h2 (q : Pattern) (selected : d153152 q = 0) : d155060 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153152, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13775 q selected
    | true =>
      simp only [d153152, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153244 q = 0) : d155115 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153244, d155115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153244, d155115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153153 q = 0) : d155061 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153153, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153153, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153245 q = 0) : d155116 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153245, d155116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153245, d155116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153246 q = 0) : d155117 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153246, d155117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153246, d155117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290866 q = 0) : d292398 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290866, d292398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290866, d292398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290867 q = 0) : d292399 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d290867, d292399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290867, d292399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30642 (p : Pattern) (selected : d290877 p = 0) : d292413 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290868 q = 0) : d292400 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290868, d292400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30640 q selected
    | true =>
      simp only [d290868, d292400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30641 q selected
  have h2 (q : Pattern) (selected : d290869 q = 0) : d292401 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290869, d292401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290869, d292401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290870 q = 0) : d292402 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290870, d292402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290870, d292402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290871 q = 0) : d292403 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290871, d292403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30641 q selected
    | true =>
      simp only [d290871, d292403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290872 q = 0) : d292404 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290872, d292404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290872, d292404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290873 q = 0) : d292405 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290873, d292405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290873, d292405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290874 q = 0) : d292406 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290874, d292406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290874, d292406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290875 q = 0) : d292411 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290875, d292411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290875, d292411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290876 q = 0) : d292412 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d290876, d292412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290876, d292412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290877 q = 0) : d292413 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d290877, d292413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290877, d292413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30643 (p : Pattern) (selected : d290881 p = 0) : d292421 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290871 q = 0) : d292403 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290871, d292403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30641 q selected
    | true =>
      simp only [d290871, d292403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290872 q = 0) : d292404 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290872, d292404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290872, d292404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290873 q = 0) : d292405 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290873, d292405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290873, d292405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290875 q = 0) : d292411 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290875, d292411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290875, d292411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290880 q = 0) : d292420 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d290880, d292420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290880, d292420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290881 q = 0) : d292421 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d290881, d292421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290881, d292421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30644 (p : Pattern) (selected : d290887 p = 0) : d292427 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290878 q = 0) : d292414 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290878, d292414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30642 q selected
    | true =>
      simp only [d290878, d292414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290879 q = 0) : d292415 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290879, d292415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290879, d292415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290882 q = 0) : d292422 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290882, d292422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30643 q selected
    | true =>
      simp only [d290882, d292422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290883 q = 0) : d292423 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290883, d292423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290883, d292423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290884 q = 0) : d292424 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290884, d292424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290884, d292424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290885 q = 0) : d292425 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290885, d292425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290885, d292425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290886 q = 0) : d292426 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290886, d292426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290886, d292426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290887 q = 0) : d292427 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290887, d292427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290887, d292427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30645 (p : Pattern) (selected : d290891 p = 0) : d292432 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290882 q = 0) : d292422 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290882, d292422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30643 q selected
    | true =>
      simp only [d290882, d292422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290883 q = 0) : d292423 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290883, d292423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290883, d292423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290888 q = 0) : d292429 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290888, d292429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290888, d292429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290889 q = 0) : d292430 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290889, d292430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290889, d292430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290890 q = 0) : d292431 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290890, d292431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290890, d292431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290891 q = 0) : d292432 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290891, d292432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290891, d292432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30646 (p : Pattern) (selected : d290897 p = 0) : d292438 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290840 q = 0) : d292414 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290840, d292414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30636 q selected
    | true =>
      simp only [d290840, d292414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290841 q = 0) : d292415 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290841, d292415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290841, d292415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290894 q = 0) : d292435 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290894, d292435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290894, d292435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290895 q = 0) : d292436 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290895, d292436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290895, d292436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290896 q = 0) : d292437 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290896, d292437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290896, d292437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290897 q = 0) : d292438 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290897, d292438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290897, d292438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30647 (p : Pattern) (selected : d290903 p = 0) : d292444 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290854 q = 0) : d292428 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290854, d292428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30637 q selected
    | true =>
      simp only [d290854, d292428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30639 q selected
  have h2 (q : Pattern) (selected : d290892 q = 0) : d292433 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290892, d292433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30644 q selected
    | true =>
      simp only [d290892, d292433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30645 q selected
  have h3 (q : Pattern) (selected : d290893 q = 0) : d292434 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290893, d292434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290893, d292434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290898 q = 0) : d292439 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290898, d292439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30646 q selected
    | true =>
      simp only [d290898, d292439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290899 q = 0) : d292440 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290899, d292440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290899, d292440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290900 q = 0) : d292441 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290900, d292441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290900, d292441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290901 q = 0) : d292442 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290901, d292442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290901, d292442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290902 q = 0) : d292443 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290902, d292443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290902, d292443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d290903 q = 0) : d292444 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290903, d292444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290903, d292444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro30648 (p : Pattern) (selected : d290908 p = 0) : d292432 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290848 q = 0) : d292422 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290848, d292422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30638 q selected
    | true =>
      simp only [d290848, d292422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290849 q = 0) : d292423 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290849, d292423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290849, d292423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290905 q = 0) : d292429 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290905, d292429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290905, d292429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290906 q = 0) : d292430 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290906, d292430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290906, d292430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290907 q = 0) : d292431 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290907, d292431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290907, d292431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290908 q = 0) : d292432 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290908, d292432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290908, d292432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30649 (p : Pattern) (selected : d290914 p = 0) : d292451 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290909 q = 0) : d292446 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290909, d292446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30648 q selected
    | true =>
      simp only [d290909, d292446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290910 q = 0) : d292447 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290910, d292447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290910, d292447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290911 q = 0) : d292448 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290911, d292448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290911, d292448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290912 q = 0) : d292449 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290912, d292449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290912, d292449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290913 q = 0) : d292450 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290913, d292450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290913, d292450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290914 q = 0) : d292451 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290914, d292451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290914, d292451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30650 (p : Pattern) (selected : d290920 p = 0) : d292457 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290637 q = 0) : d292256 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290637, d292256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290637, d292256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30594 q selected
  have h2 (q : Pattern) (selected : d290638 q = 0) : d292257 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290638, d292257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290638, d292257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d290647 q = 0) : d292266 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290647, d292266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30594 q selected
    | true =>
      simp only [d290647, d292266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30597 q selected
  have h4 (q : Pattern) (selected : d290648 q = 0) : d292267 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290648, d292267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290648, d292267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290649 q = 0) : d292268 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290649, d292268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290649, d292268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290776 q = 0) : d292350 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290776, d292350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30617 q selected
    | true =>
      simp only [d290776, d292350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30626 q selected
  have h7 (q : Pattern) (selected : d290789 q = 0) : d292363 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290789, d292363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30627 q selected
    | true =>
      simp only [d290789, d292363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30628 q selected
  have h8 (q : Pattern) (selected : d290790 q = 0) : d292364 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290790, d292364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290790, d292364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d290791 q = 0) : d292365 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290791, d292365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290791, d292365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d290792 q = 0) : d292366 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290792, d292366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290792, d292366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d290796 q = 0) : d292370 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290796, d292370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290796, d292370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30629 q selected
  have h12 (q : Pattern) (selected : d290798 q = 0) : d292372 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290798, d292372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290798, d292372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30630 q selected
  have h13 (q : Pattern) (selected : d290799 q = 0) : d292373 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290799, d292373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d290799, d292373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d290800 q = 0) : d292374 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290800, d292374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d290800, d292374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d290801 q = 0) : d292375 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290801, d292375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d290801, d292375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d290802 q = 0) : d292376 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290802, d292376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d290802, d292376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d290904 q = 0) : d292445 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290904, d292445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290904, d292445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30647 q selected
  have h18 (q : Pattern) (selected : d290915 q = 0) : d292452 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290915, d292452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290915, d292452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30649 q selected
  have h19 (q : Pattern) (selected : d290916 q = 0) : d292453 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290916, d292453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d290916, d292453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d290917 q = 0) : d292454 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290917, d292454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d290917, d292454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d290918 q = 0) : d292455 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290918, d292455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d290918, d292455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d290919 q = 0) : d292456 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290919, d292456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d290919, d292456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d290920 q = 0) : d292457 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290920, d292457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d290920, d292457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro30651 (p : Pattern) (selected : d290926 p = 0) : d292463 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290921 q = 0) : d292458 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290921, d292458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290921, d292458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30650 q selected
  have h2 (q : Pattern) (selected : d290922 q = 0) : d292459 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290922, d292459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290922, d292459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290923 q = 0) : d292460 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290923, d292460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290923, d292460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290924 q = 0) : d292461 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290924, d292461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290924, d292461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290925 q = 0) : d292462 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290925, d292462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290925, d292462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290926 q = 0) : d292463 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290926, d292463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290926, d292463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30652 (p : Pattern) (selected : d290930 p = 0) : d292467 p = 1 := by
  have h0 (q : Pattern) (selected : d1088 q = 0) : d52669 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro275 q selected
    | true =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro384 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1089 q = 0) : d52670 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25765 q = 0) : d199013 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25765, d199013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18806 q selected
    | true =>
      simp only [d25765, d199013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d25766 q = 0) : d199014 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25766, d199014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25766, d199014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d290929 q = 0) : d292466 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d290929, d292466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290929, d292466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290930 q = 0) : d292467 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d290930, d292467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290930, d292467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro30653 (p : Pattern) (selected : d290936 p = 0) : d292473 p = 1 := by
  have h0 (q : Pattern) (selected : d1094 q = 0) : d52675 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro234 q selected
    | true =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro385 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1095 q = 0) : d52676 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290935 q = 0) : d292472 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d290935, d292472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290935, d292472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d290936 q = 0) : d292473 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d290936, d292473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290936, d292473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h4 p selected
theorem eqIntro30654 (p : Pattern) (selected : d290943 p = 0) : d292480 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1115 q = 0) : d52696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
  have h2 (q : Pattern) (selected : d1116 q = 0) : d52697 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, d52697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1116, d52697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d19 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290942 q = 0) : d292479 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d290942, d292479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290942, d292479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290943 q = 0) : d292480 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d290943, d292480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290943, d292480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30655 (p : Pattern) (selected : d290949 p = 0) : d292486 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290931 q = 0) : d292468 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290931, d292468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30652 q selected
    | true =>
      simp only [d290931, d292468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290932 q = 0) : d292469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290932, d292469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290932, d292469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d290933 q = 0) : d292470 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290933, d292470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290933, d292470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290934 q = 0) : d292471 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290934, d292471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290934, d292471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290937 q = 0) : d292474 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290937, d292474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30653 q selected
    | true =>
      simp only [d290937, d292474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290938 q = 0) : d292475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290938, d292475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290938, d292475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290939 q = 0) : d292476 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290939, d292476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290939, d292476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290940 q = 0) : d292477 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290940, d292477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290940, d292477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290941 q = 0) : d292478 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290941, d292478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290941, d292478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290944 q = 0) : d292481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290944, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30654 q selected
    | true =>
      simp only [d290944, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d290945 q = 0) : d292482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290945, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d290945, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d290946 q = 0) : d292483 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290946, d292483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290946, d292483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d290947 q = 0) : d292484 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290947, d292484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d290947, d292484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d290948 q = 0) : d292485 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290948, d292485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290948, d292485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d290949 q = 0) : d292486 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d290949, d292486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290949, d292486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30656 (p : Pattern) (selected : d290951 p = 0) : d292488 p = 1 := by
  have h0 (q : Pattern) (selected : d1094 q = 0) : d52675 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro234 q selected
    | true =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro385 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1095 q = 0) : d52676 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25433 q = 0) : d198756 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d198756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18742 q selected
    | true =>
      simp only [d25433, d198756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d25434 q = 0) : d198757 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d198757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25434, d198757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d290950 q = 0) : d292487 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d290950, d292487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290950, d292487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290951 q = 0) : d292488 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d290951, d292488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290951, d292488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro30657 (p : Pattern) (selected : d290958 p = 0) : d292495 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290952 q = 0) : d292489 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290952, d292489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30656 q selected
    | true =>
      simp only [d290952, d292489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290953 q = 0) : d292490 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290953, d292490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290953, d292490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d290954 q = 0) : d292491 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290954, d292491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290954, d292491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290955 q = 0) : d292492 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290955, d292492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290955, d292492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290944 q = 0) : d292481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290944, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30654 q selected
    | true =>
      simp only [d290944, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290945 q = 0) : d292482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290945, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290945, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290946 q = 0) : d292483 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290946, d292483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290946, d292483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290947 q = 0) : d292484 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290947, d292484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290947, d292484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290956 q = 0) : d292493 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290956, d292493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290956, d292493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290957 q = 0) : d292494 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290957, d292494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290957, d292494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d290958 q = 0) : d292495 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d290958, d292495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290958, d292495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30658 (p : Pattern) (selected : d290962 p = 0) : d292499 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290944 q = 0) : d292481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290944, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30654 q selected
    | true =>
      simp only [d290944, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290945 q = 0) : d292482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290945, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290945, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d290946 q = 0) : d292483 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290946, d292483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290946, d292483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290947 q = 0) : d292484 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290947, d292484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290947, d292484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290957 q = 0) : d292494 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290957, d292494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290957, d292494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290962 q = 0) : d292499 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d290962, d292499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290962, d292499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30659 (p : Pattern) (selected : d290969 p = 0) : d292506 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290959 q = 0) : d292496 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290959, d292496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30655 q selected
    | true =>
      simp only [d290959, d292496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30657 q selected
  have h2 (q : Pattern) (selected : d290960 q = 0) : d292497 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290960, d292497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290960, d292497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290961 q = 0) : d292498 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290961, d292498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290961, d292498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290963 q = 0) : d292500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290963, d292500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30657 q selected
    | true =>
      simp only [d290963, d292500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30658 q selected
  have h5 (q : Pattern) (selected : d290964 q = 0) : d292501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290964, d292501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290964, d292501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290965 q = 0) : d292502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290965, d292502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290965, d292502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290966 q = 0) : d292503 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290966, d292503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290966, d292503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290967 q = 0) : d292504 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290967, d292504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290967, d292504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290968 q = 0) : d292505 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d290968, d292505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290968, d292505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290969 q = 0) : d292506 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d290969, d292506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290969, d292506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30660 (p : Pattern) (selected : d290973 p = 0) : d292510 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290963 q = 0) : d292500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290963, d292500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30657 q selected
    | true =>
      simp only [d290963, d292500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30658 q selected
  have h2 (q : Pattern) (selected : d290964 q = 0) : d292501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290964, d292501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290964, d292501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290965 q = 0) : d292502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290965, d292502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290965, d292502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290967 q = 0) : d292504 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290967, d292504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290967, d292504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290972 q = 0) : d292509 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d290972, d292509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290972, d292509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290973 q = 0) : d292510 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d290973, d292510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290973, d292510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30661 (p : Pattern) (selected : d290979 p = 0) : d292516 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290970 q = 0) : d292507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290970, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30659 q selected
    | true =>
      simp only [d290970, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290971 q = 0) : d292508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290971, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290971, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290974 q = 0) : d292511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30660 q selected
    | true =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290975 q = 0) : d292512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290976 q = 0) : d292513 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290976, d292513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290976, d292513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290977 q = 0) : d292514 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290977, d292514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290977, d292514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290978 q = 0) : d292515 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290978, d292515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290978, d292515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290979 q = 0) : d292516 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290979, d292516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290979, d292516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30662 (p : Pattern) (selected : d290983 p = 0) : d292520 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290974 q = 0) : d292511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30660 q selected
    | true =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290975 q = 0) : d292512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290980 q = 0) : d292517 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290980, d292517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290980, d292517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290981 q = 0) : d292518 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290981, d292518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290981, d292518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290982 q = 0) : d292519 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290982, d292519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290982, d292519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290983 q = 0) : d292520 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290983, d292520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290983, d292520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30663 (p : Pattern) (selected : d290989 p = 0) : d292526 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290984 q = 0) : d292521 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290984, d292521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30661 q selected
    | true =>
      simp only [d290984, d292521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30662 q selected
  have h2 (q : Pattern) (selected : d290985 q = 0) : d292522 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290985, d292522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290985, d292522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290986 q = 0) : d292523 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290986, d292523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290986, d292523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290987 q = 0) : d292524 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290987, d292524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290987, d292524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290988 q = 0) : d292525 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290988, d292525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290988, d292525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290989 q = 0) : d292526 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290989, d292526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290989, d292526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30664 (p : Pattern) (selected : d290992 p = 0) : d292529 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290970 q = 0) : d292507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290970, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30659 q selected
    | true =>
      simp only [d290970, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290971 q = 0) : d292508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290971, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290971, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290974 q = 0) : d292511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30660 q selected
    | true =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290975 q = 0) : d292512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290976 q = 0) : d292513 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290976, d292513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290976, d292513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290977 q = 0) : d292514 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290977, d292514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290977, d292514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290978 q = 0) : d292515 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290978, d292515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290978, d292515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290992 q = 0) : d292529 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290992, d292529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290992, d292529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30665 (p : Pattern) (selected : d290993 p = 0) : d292530 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290974 q = 0) : d292511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30660 q selected
    | true =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290975 q = 0) : d292512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290980 q = 0) : d292517 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290980, d292517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290980, d292517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290981 q = 0) : d292518 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290981, d292518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290981, d292518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290982 q = 0) : d292519 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290982, d292519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290982, d292519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290993 q = 0) : d292530 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290993, d292530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290993, d292530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30666 (p : Pattern) (selected : d290999 p = 0) : d292536 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290984 q = 0) : d292521 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290984, d292521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30661 q selected
    | true =>
      simp only [d290984, d292521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30662 q selected
  have h2 (q : Pattern) (selected : d290985 q = 0) : d292522 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290985, d292522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290985, d292522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290986 q = 0) : d292523 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290986, d292523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290986, d292523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290987 q = 0) : d292524 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290987, d292524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290987, d292524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290988 q = 0) : d292525 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290988, d292525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290988, d292525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290994 q = 0) : d292531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290994, d292531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30664 q selected
    | true =>
      simp only [d290994, d292531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30665 q selected
  have h7 (q : Pattern) (selected : d290995 q = 0) : d292532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290995, d292532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290995, d292532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290996 q = 0) : d292533 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290996, d292533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290996, d292533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290997 q = 0) : d292534 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290997, d292534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290997, d292534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290998 q = 0) : d292535 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290998, d292535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290998, d292535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d290999 q = 0) : d292536 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290999, d292536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290999, d292536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30667 (p : Pattern) (selected : d291004 p = 0) : d292541 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290970 q = 0) : d292507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290970, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30659 q selected
    | true =>
      simp only [d290970, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290971 q = 0) : d292508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290971, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290971, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290974 q = 0) : d292511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30660 q selected
    | true =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290975 q = 0) : d292512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290976 q = 0) : d292513 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290976, d292513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290976, d292513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290977 q = 0) : d292514 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290977, d292514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290977, d292514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291003 q = 0) : d292540 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291003, d292540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291003, d292540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291004 q = 0) : d292541 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291004, d292541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291004, d292541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30668 (p : Pattern) (selected : d291006 p = 0) : d292543 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290974 q = 0) : d292511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30660 q selected
    | true =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290975 q = 0) : d292512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290980 q = 0) : d292517 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290980, d292517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290980, d292517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290981 q = 0) : d292518 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290981, d292518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290981, d292518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291005 q = 0) : d292542 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291005, d292542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291005, d292542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291006 q = 0) : d292543 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291006, d292543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291006, d292543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30669 (p : Pattern) (selected : d291013 p = 0) : d292550 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290970 q = 0) : d292507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290970, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30659 q selected
    | true =>
      simp only [d290970, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290971 q = 0) : d292508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290971, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290971, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290974 q = 0) : d292511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30660 q selected
    | true =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290975 q = 0) : d292512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290976 q = 0) : d292513 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290976, d292513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290976, d292513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291011 q = 0) : d292548 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291011, d292548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291011, d292548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291012 q = 0) : d292549 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291012, d292549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291012, d292549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291013 q = 0) : d292550 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291013, d292550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291013, d292550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30670 (p : Pattern) (selected : d291016 p = 0) : d292553 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290974 q = 0) : d292511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30660 q selected
    | true =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290975 q = 0) : d292512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290980 q = 0) : d292517 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290980, d292517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290980, d292517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291014 q = 0) : d292551 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291014, d292551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291014, d292551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291015 q = 0) : d292552 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291015, d292552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291015, d292552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291016 q = 0) : d292553 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291016, d292553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291016, d292553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30671 (p : Pattern) (selected : d291021 p = 0) : d292558 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d822 q = 0) : d52499 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro333 q selected
    | true =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d823 q = 0) : d52500 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291020 q = 0) : d292557 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291020, d292557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291020, d292557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291021 q = 0) : d292558 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291021, d292558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291021, d292558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro30672 (p : Pattern) (selected : d291027 p = 0) : d292564 p = 1 := by
  have h0 (q : Pattern) (selected : d1088 q = 0) : d52669 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro275 q selected
    | true =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro384 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1089 q = 0) : d52670 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291026 q = 0) : d292563 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291026, d292563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291026, d292563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d291027 q = 0) : d292564 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291027, d292564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291027, d292564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h4 p selected
theorem eqIntro30673 (p : Pattern) (selected : d291034 p = 0) : d292571 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291022 q = 0) : d292559 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291022, d292559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30671 q selected
    | true =>
      simp only [d291022, d292559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291023 q = 0) : d292560 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291023, d292560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291023, d292560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291024 q = 0) : d292561 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291024, d292561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291024, d292561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291025 q = 0) : d292562 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291025, d292562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291025, d292562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291028 q = 0) : d292565 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291028, d292565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30672 q selected
    | true =>
      simp only [d291028, d292565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291029 q = 0) : d292566 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291029, d292566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291029, d292566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291030 q = 0) : d292567 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291030, d292567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291030, d292567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291031 q = 0) : d292568 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291031, d292568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291031, d292568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291032 q = 0) : d292569 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291032, d292569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291032, d292569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290937 q = 0) : d292474 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290937, d292474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30653 q selected
    | true =>
      simp only [d290937, d292474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d290938 q = 0) : d292475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290938, d292475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d290938, d292475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d290939 q = 0) : d292476 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290939, d292476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290939, d292476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d290940 q = 0) : d292477 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290940, d292477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d290940, d292477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d291033 q = 0) : d292570 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291033, d292570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291033, d292570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d291034 q = 0) : d292571 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291034, d292571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291034, d292571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30674 (p : Pattern) (selected : d291038 p = 0) : d292575 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290937 q = 0) : d292474 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290937, d292474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30653 q selected
    | true =>
      simp only [d290937, d292474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290938 q = 0) : d292475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290938, d292475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290938, d292475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d290939 q = 0) : d292476 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290939, d292476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290939, d292476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290940 q = 0) : d292477 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290940, d292477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290940, d292477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290944 q = 0) : d292481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290944, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30654 q selected
    | true =>
      simp only [d290944, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290945 q = 0) : d292482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290945, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290945, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290946 q = 0) : d292483 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290946, d292483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290946, d292483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290947 q = 0) : d292484 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290947, d292484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290947, d292484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290948 q = 0) : d292485 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290948, d292485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290948, d292485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290957 q = 0) : d292494 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290957, d292494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290957, d292494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291038 q = 0) : d292575 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291038, d292575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291038, d292575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30675 (p : Pattern) (selected : d291044 p = 0) : d292581 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291035 q = 0) : d292572 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291035, d292572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30673 q selected
    | true =>
      simp only [d291035, d292572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30655 q selected
  have h2 (q : Pattern) (selected : d291036 q = 0) : d292573 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291036, d292573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291036, d292573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291037 q = 0) : d292574 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291037, d292574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291037, d292574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291039 q = 0) : d292576 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291039, d292576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30655 q selected
    | true =>
      simp only [d291039, d292576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30674 q selected
  have h5 (q : Pattern) (selected : d291040 q = 0) : d292577 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291040, d292577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291040, d292577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291041 q = 0) : d292578 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291041, d292578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291041, d292578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291042 q = 0) : d292579 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291042, d292579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291042, d292579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290959 q = 0) : d292496 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290959, d292496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30655 q selected
    | true =>
      simp only [d290959, d292496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30657 q selected
  have h9 (q : Pattern) (selected : d290960 q = 0) : d292497 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290960, d292497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290960, d292497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290961 q = 0) : d292498 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290961, d292498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290961, d292498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d290963 q = 0) : d292500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290963, d292500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30657 q selected
    | true =>
      simp only [d290963, d292500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30658 q selected
  have h12 (q : Pattern) (selected : d290964 q = 0) : d292501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290964, d292501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290964, d292501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d290965 q = 0) : d292502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290965, d292502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290965, d292502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d290966 q = 0) : d292503 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290966, d292503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d290966, d292503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d291043 q = 0) : d292580 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291043, d292580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291043, d292580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d291044 q = 0) : d292581 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291044, d292581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d291044, d292581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro30676 (p : Pattern) (selected : d291050 p = 0) : d292587 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291045 q = 0) : d292582 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291045, d292582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30675 q selected
    | true =>
      simp only [d291045, d292582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291046 q = 0) : d292583 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291046, d292583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291046, d292583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290970 q = 0) : d292507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290970, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30659 q selected
    | true =>
      simp only [d290970, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290971 q = 0) : d292508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290971, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290971, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291047 q = 0) : d292584 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291047, d292584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291047, d292584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291048 q = 0) : d292585 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291048, d292585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291048, d292585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291049 q = 0) : d292586 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291049, d292586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291049, d292586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291050 q = 0) : d292587 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291050, d292587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291050, d292587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30677 (p : Pattern) (selected : d291053 p = 0) : d292467 p = 1 := by
  have h0 (q : Pattern) (selected : d1237 q = 0) : d52669 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1237, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro339 q selected
    | true =>
      simp only [d1237, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro412 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1238 q = 0) : d52670 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1238, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1238, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d26229 q = 0) : d199013 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d26229, d199013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18891 q selected
    | true =>
      simp only [d26229, d199013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d26230 q = 0) : d199014 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d26230, d199014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d26230, d199014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d291052 q = 0) : d292466 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291052, d292466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291052, d292466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291053 q = 0) : d292467 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291053, d292467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291053, d292467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro30678 (p : Pattern) (selected : d291059 p = 0) : d292473 p = 1 := by
  have h0 (q : Pattern) (selected : d1249 q = 0) : d52675 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1249, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro281 q selected
    | true =>
      simp only [d1249, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro414 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1250 q = 0) : d52676 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1250, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1250, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291058 q = 0) : d292472 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291058, d292472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291058, d292472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d291059 q = 0) : d292473 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291059, d292473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291059, d292473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h4 p selected
theorem eqIntro30679 (p : Pattern) (selected : d291066 p = 0) : d292480 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1270 q = 0) : d52696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
  have h2 (q : Pattern) (selected : d1271 q = 0) : d52697 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1271, d52697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1271, d52697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291065 q = 0) : d292479 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291065, d292479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291065, d292479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291066 q = 0) : d292480 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291066, d292480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291066, d292480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30680 (p : Pattern) (selected : d291072 p = 0) : d292486 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291054 q = 0) : d292468 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291054, d292468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30677 q selected
    | true =>
      simp only [d291054, d292468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291055 q = 0) : d292469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291055, d292469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291055, d292469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291056 q = 0) : d292470 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291056, d292470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291056, d292470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291057 q = 0) : d292471 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291057, d292471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291057, d292471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291060 q = 0) : d292474 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291060, d292474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30678 q selected
    | true =>
      simp only [d291060, d292474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291061 q = 0) : d292475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291061, d292475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291061, d292475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291062 q = 0) : d292476 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291062, d292476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291062, d292476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291063 q = 0) : d292477 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291063, d292477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291063, d292477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291064 q = 0) : d292478 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291064, d292478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291064, d292478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291067 q = 0) : d292481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291067, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30679 q selected
    | true =>
      simp only [d291067, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291068 q = 0) : d292482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291068, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291068, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d291069 q = 0) : d292483 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291069, d292483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291069, d292483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d291070 q = 0) : d292484 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291070, d292484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291070, d292484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d291071 q = 0) : d292485 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291071, d292485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291071, d292485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d291072 q = 0) : d292486 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291072, d292486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291072, d292486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30681 (p : Pattern) (selected : d291074 p = 0) : d292488 p = 1 := by
  have h0 (q : Pattern) (selected : d1249 q = 0) : d52675 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1249, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro281 q selected
    | true =>
      simp only [d1249, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro414 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1250 q = 0) : d52676 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1250, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1250, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25812 q = 0) : d198756 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25812, d198756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18814 q selected
    | true =>
      simp only [d25812, d198756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d25813 q = 0) : d198757 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25813, d198757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25813, d198757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d291073 q = 0) : d292487 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291073, d292487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291073, d292487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291074 q = 0) : d292488 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291074, d292488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291074, d292488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro30682 (p : Pattern) (selected : d291081 p = 0) : d292495 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291075 q = 0) : d292489 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291075, d292489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30681 q selected
    | true =>
      simp only [d291075, d292489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291076 q = 0) : d292490 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291076, d292490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291076, d292490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291077 q = 0) : d292491 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291077, d292491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291077, d292491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291078 q = 0) : d292492 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291078, d292492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291078, d292492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291067 q = 0) : d292481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291067, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30679 q selected
    | true =>
      simp only [d291067, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291068 q = 0) : d292482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291068, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291068, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291069 q = 0) : d292483 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291069, d292483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291069, d292483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291070 q = 0) : d292484 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291070, d292484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291070, d292484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291079 q = 0) : d292493 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291079, d292493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291079, d292493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291080 q = 0) : d292494 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291080, d292494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291080, d292494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291081 q = 0) : d292495 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291081, d292495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291081, d292495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30683 (p : Pattern) (selected : d291085 p = 0) : d292499 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291067 q = 0) : d292481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291067, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30679 q selected
    | true =>
      simp only [d291067, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291068 q = 0) : d292482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291068, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291068, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291069 q = 0) : d292483 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291069, d292483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291069, d292483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291070 q = 0) : d292484 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291070, d292484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291070, d292484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291080 q = 0) : d292494 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291080, d292494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291080, d292494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291085 q = 0) : d292499 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291085, d292499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291085, d292499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30684 (p : Pattern) (selected : d291092 p = 0) : d292506 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291082 q = 0) : d292496 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291082, d292496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30680 q selected
    | true =>
      simp only [d291082, d292496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30682 q selected
  have h2 (q : Pattern) (selected : d291083 q = 0) : d292497 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291083, d292497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291083, d292497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291084 q = 0) : d292498 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291084, d292498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291084, d292498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291086 q = 0) : d292500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291086, d292500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30682 q selected
    | true =>
      simp only [d291086, d292500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30683 q selected
  have h5 (q : Pattern) (selected : d291087 q = 0) : d292501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291087, d292501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291087, d292501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291088 q = 0) : d292502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291088, d292502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291088, d292502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291089 q = 0) : d292503 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291089, d292503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291089, d292503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291090 q = 0) : d292504 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291090, d292504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291090, d292504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291091 q = 0) : d292505 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291091, d292505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291091, d292505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291092 q = 0) : d292506 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291092, d292506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291092, d292506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30685 (p : Pattern) (selected : d291096 p = 0) : d292510 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291086 q = 0) : d292500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291086, d292500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30682 q selected
    | true =>
      simp only [d291086, d292500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30683 q selected
  have h2 (q : Pattern) (selected : d291087 q = 0) : d292501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291087, d292501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291087, d292501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291088 q = 0) : d292502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291088, d292502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291088, d292502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291090 q = 0) : d292504 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291090, d292504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291090, d292504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291095 q = 0) : d292509 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291095, d292509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291095, d292509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291096 q = 0) : d292510 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291096, d292510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291096, d292510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30686 (p : Pattern) (selected : d291102 p = 0) : d292516 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291093 q = 0) : d292507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291093, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30684 q selected
    | true =>
      simp only [d291093, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291094 q = 0) : d292508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291094, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291094, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291097 q = 0) : d292511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291097, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30685 q selected
    | true =>
      simp only [d291097, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291098 q = 0) : d292512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291098, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291098, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291099 q = 0) : d292513 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291099, d292513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291099, d292513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291100 q = 0) : d292514 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291100, d292514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291100, d292514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291101 q = 0) : d292515 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291101, d292515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291101, d292515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291102 q = 0) : d292516 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291102, d292516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291102, d292516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30687 (p : Pattern) (selected : d291106 p = 0) : d292520 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291097 q = 0) : d292511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291097, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30685 q selected
    | true =>
      simp only [d291097, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291098 q = 0) : d292512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291098, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291098, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291103 q = 0) : d292517 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291103, d292517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291103, d292517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291104 q = 0) : d292518 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291104, d292518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291104, d292518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291105 q = 0) : d292519 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291105, d292519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291105, d292519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291106 q = 0) : d292520 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291106, d292520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291106, d292520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30688 (p : Pattern) (selected : d291112 p = 0) : d292593 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290970 q = 0) : d292507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290970, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30659 q selected
    | true =>
      simp only [d290970, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290971 q = 0) : d292508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290971, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290971, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291109 q = 0) : d292590 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291109, d292590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291109, d292590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291110 q = 0) : d292591 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291110, d292591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291110, d292591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291111 q = 0) : d292592 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291111, d292592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291111, d292592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291112 q = 0) : d292593 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291112, d292593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291112, d292593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30689 (p : Pattern) (selected : d291118 p = 0) : d292599 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291007 q = 0) : d292544 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291007, d292544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30667 q selected
    | true =>
      simp only [d291007, d292544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30668 q selected
  have h2 (q : Pattern) (selected : d291008 q = 0) : d292545 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291008, d292545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291008, d292545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291009 q = 0) : d292546 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291009, d292546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291009, d292546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291010 q = 0) : d292547 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291010, d292547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291010, d292547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291017 q = 0) : d292554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291017, d292554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30669 q selected
    | true =>
      simp only [d291017, d292554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30670 q selected
  have h6 (q : Pattern) (selected : d291018 q = 0) : d292555 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291018, d292555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291018, d292555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291019 q = 0) : d292556 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291019, d292556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291019, d292556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291051 q = 0) : d292588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291051, d292588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30676 q selected
    | true =>
      simp only [d291051, d292588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30661 q selected
  have h9 (q : Pattern) (selected : d291107 q = 0) : d292521 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291107, d292521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30686 q selected
    | true =>
      simp only [d291107, d292521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30687 q selected
  have h10 (q : Pattern) (selected : d291108 q = 0) : d292589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291108, d292589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291108, d292589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291113 q = 0) : d292594 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291113, d292594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30688 q selected
    | true =>
      simp only [d291113, d292594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d291114 q = 0) : d292595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291114, d292595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291114, d292595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291115 q = 0) : d292596 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291115, d292596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291115, d292596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291116 q = 0) : d292597 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291116, d292597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291116, d292597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d291117 q = 0) : d292598 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291117, d292598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291117, d292598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d291118 q = 0) : d292599 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291118, d292599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291118, d292599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro30690 (p : Pattern) (selected : d291119 p = 0) : d292600 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290970 q = 0) : d292507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290970, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30659 q selected
    | true =>
      simp only [d290970, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290971 q = 0) : d292508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290971, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290971, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290974 q = 0) : d292511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30660 q selected
    | true =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290975 q = 0) : d292512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290976 q = 0) : d292513 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290976, d292513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290976, d292513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290977 q = 0) : d292514 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290977, d292514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290977, d292514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291003 q = 0) : d292540 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291003, d292540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291003, d292540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291119 q = 0) : d292600 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291119, d292600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291119, d292600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30691 (p : Pattern) (selected : d291120 p = 0) : d292601 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290974 q = 0) : d292511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30660 q selected
    | true =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290975 q = 0) : d292512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290980 q = 0) : d292517 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290980, d292517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290980, d292517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290981 q = 0) : d292518 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290981, d292518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290981, d292518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291005 q = 0) : d292542 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291005, d292542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291005, d292542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291120 q = 0) : d292601 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291120, d292601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291120, d292601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30692 (p : Pattern) (selected : d291125 p = 0) : d292606 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290970 q = 0) : d292507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290970, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30659 q selected
    | true =>
      simp only [d290970, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290971 q = 0) : d292508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290971, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290971, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290974 q = 0) : d292511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30660 q selected
    | true =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290975 q = 0) : d292512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290976 q = 0) : d292513 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290976, d292513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290976, d292513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291011 q = 0) : d292548 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291011, d292548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291011, d292548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291012 q = 0) : d292549 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291012, d292549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291012, d292549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291125 q = 0) : d292606 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291125, d292606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291125, d292606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30693 (p : Pattern) (selected : d291126 p = 0) : d292607 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290974 q = 0) : d292511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30660 q selected
    | true =>
      simp only [d290974, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290975 q = 0) : d292512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290975, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290980 q = 0) : d292517 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290980, d292517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290980, d292517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291014 q = 0) : d292551 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291014, d292551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291014, d292551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291015 q = 0) : d292552 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291015, d292552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291015, d292552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291126 q = 0) : d292607 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291126, d292607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291126, d292607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30694 (p : Pattern) (selected : d291130 p = 0) : d292611 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291045 q = 0) : d292582 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291045, d292582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30675 q selected
    | true =>
      simp only [d291045, d292582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291046 q = 0) : d292583 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291046, d292583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291046, d292583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290970 q = 0) : d292507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290970, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30659 q selected
    | true =>
      simp only [d290970, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290971 q = 0) : d292508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290971, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290971, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291047 q = 0) : d292584 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291047, d292584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291047, d292584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291048 q = 0) : d292585 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291048, d292585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291048, d292585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291049 q = 0) : d292586 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291049, d292586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291049, d292586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291130 q = 0) : d292611 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291130, d292611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291130, d292611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30695 (p : Pattern) (selected : d291132 p = 0) : d292529 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291093 q = 0) : d292507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291093, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30684 q selected
    | true =>
      simp only [d291093, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291094 q = 0) : d292508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291094, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291094, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291097 q = 0) : d292511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291097, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30685 q selected
    | true =>
      simp only [d291097, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291098 q = 0) : d292512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291098, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291098, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291099 q = 0) : d292513 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291099, d292513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291099, d292513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291100 q = 0) : d292514 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291100, d292514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291100, d292514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291101 q = 0) : d292515 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291101, d292515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291101, d292515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291132 q = 0) : d292529 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291132, d292529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291132, d292529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30696 (p : Pattern) (selected : d291133 p = 0) : d292530 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291097 q = 0) : d292511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291097, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30685 q selected
    | true =>
      simp only [d291097, d292511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291098 q = 0) : d292512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291098, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291098, d292512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291103 q = 0) : d292517 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291103, d292517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291103, d292517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291104 q = 0) : d292518 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291104, d292518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291104, d292518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291105 q = 0) : d292519 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291105, d292519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291105, d292519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291133 q = 0) : d292530 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291133, d292530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291133, d292530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30697 (p : Pattern) (selected : d291136 p = 0) : d292614 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290970 q = 0) : d292507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290970, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30659 q selected
    | true =>
      simp only [d290970, d292507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290971 q = 0) : d292508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290971, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290971, d292508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291109 q = 0) : d292590 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291109, d292590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291109, d292590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291110 q = 0) : d292591 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291110, d292591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291110, d292591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291111 q = 0) : d292592 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291111, d292592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291111, d292592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291136 q = 0) : d292614 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291136, d292614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291136, d292614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30698 (p : Pattern) (selected : d291142 p = 0) : d292620 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291007 q = 0) : d292544 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291007, d292544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30667 q selected
    | true =>
      simp only [d291007, d292544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30668 q selected
  have h2 (q : Pattern) (selected : d291008 q = 0) : d292545 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291008, d292545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291008, d292545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291009 q = 0) : d292546 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291009, d292546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291009, d292546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291010 q = 0) : d292547 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291010, d292547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291010, d292547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291017 q = 0) : d292554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291017, d292554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30669 q selected
    | true =>
      simp only [d291017, d292554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30670 q selected
  have h6 (q : Pattern) (selected : d291018 q = 0) : d292555 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291018, d292555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291018, d292555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291019 q = 0) : d292556 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291019, d292556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291019, d292556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291051 q = 0) : d292588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291051, d292588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30676 q selected
    | true =>
      simp only [d291051, d292588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30661 q selected
  have h9 (q : Pattern) (selected : d291107 q = 0) : d292521 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291107, d292521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30686 q selected
    | true =>
      simp only [d291107, d292521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30687 q selected
  have h10 (q : Pattern) (selected : d291108 q = 0) : d292589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291108, d292589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291108, d292589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291113 q = 0) : d292594 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291113, d292594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30688 q selected
    | true =>
      simp only [d291113, d292594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d291114 q = 0) : d292595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291114, d292595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291114, d292595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291115 q = 0) : d292596 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291115, d292596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291115, d292596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291116 q = 0) : d292597 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291116, d292597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291116, d292597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d291117 q = 0) : d292598 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291117, d292598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291117, d292598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d291121 q = 0) : d292602 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291121, d292602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30690 q selected
    | true =>
      simp only [d291121, d292602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30691 q selected
  have h17 (q : Pattern) (selected : d291122 q = 0) : d292603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291122, d292603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291122, d292603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d291123 q = 0) : d292604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291123, d292604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d291123, d292604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d291124 q = 0) : d292605 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291124, d292605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291124, d292605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d291127 q = 0) : d292608 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291127, d292608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30692 q selected
    | true =>
      simp only [d291127, d292608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30693 q selected
  have h21 (q : Pattern) (selected : d291128 q = 0) : d292609 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291128, d292609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291128, d292609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d291129 q = 0) : d292610 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291129, d292610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d291129, d292610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d291131 q = 0) : d292612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291131, d292612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30694 q selected
    | true =>
      simp only [d291131, d292612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30664 q selected
  have h24 (q : Pattern) (selected : d291134 q = 0) : d292531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291134, d292531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30695 q selected
    | true =>
      simp only [d291134, d292531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30696 q selected
  have h25 (q : Pattern) (selected : d291135 q = 0) : d292613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291135, d292613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d291135, d292613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d291137 q = 0) : d292615 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291137, d292615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30697 q selected
    | true =>
      simp only [d291137, d292615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d291138 q = 0) : d292616 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291138, d292616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d291138, d292616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d291139 q = 0) : d292617 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291139, d292617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d291139, d292617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d291140 q = 0) : d292618 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291140, d292618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d291140, d292618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d291141 q = 0) : d292619 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291141, d292619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d291141, d292619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d291142 q = 0) : d292620 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291142, d292620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d291142, d292620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro30699 (p : Pattern) (selected : d291149 p = 0) : d292627 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290984 q = 0) : d292521 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290984, d292521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30661 q selected
    | true =>
      simp only [d290984, d292521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30662 q selected
  have h2 (q : Pattern) (selected : d290985 q = 0) : d292522 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290985, d292522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290985, d292522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290986 q = 0) : d292523 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290986, d292523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290986, d292523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290987 q = 0) : d292524 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290987, d292524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290987, d292524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290988 q = 0) : d292525 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290988, d292525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290988, d292525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291144 q = 0) : d292622 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291144, d292622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30662 q selected
    | true =>
      simp only [d291144, d292622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291145 q = 0) : d292623 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291145, d292623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291145, d292623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291146 q = 0) : d292624 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291146, d292624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291146, d292624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291147 q = 0) : d292625 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291147, d292625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291147, d292625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291148 q = 0) : d292626 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291148, d292626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291148, d292626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291149 q = 0) : d292627 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291149, d292627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291149, d292627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30700 (p : Pattern) (selected : d291155 p = 0) : d292633 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291144 q = 0) : d292622 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291144, d292622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30662 q selected
    | true =>
      simp only [d291144, d292622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291145 q = 0) : d292623 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291145, d292623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291145, d292623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291146 q = 0) : d292624 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291146, d292624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291146, d292624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291147 q = 0) : d292625 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291147, d292625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291147, d292625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291148 q = 0) : d292626 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291148, d292626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291148, d292626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291150 q = 0) : d292628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291150, d292628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30665 q selected
    | true =>
      simp only [d291150, d292628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291151 q = 0) : d292629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291151, d292629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291151, d292629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291152 q = 0) : d292630 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291152, d292630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291152, d292630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291153 q = 0) : d292631 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291153, d292631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291153, d292631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291154 q = 0) : d292632 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291154, d292632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291154, d292632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291155 q = 0) : d292633 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291155, d292633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291155, d292633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30701 (p : Pattern) (selected : d291162 p = 0) : d292640 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291131 q = 0) : d292612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291131, d292612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30694 q selected
    | true =>
      simp only [d291131, d292612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30664 q selected
  have h2 (q : Pattern) (selected : d291134 q = 0) : d292531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291134, d292531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30695 q selected
    | true =>
      simp only [d291134, d292531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30696 q selected
  have h3 (q : Pattern) (selected : d291135 q = 0) : d292613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291135, d292613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291135, d292613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291137 q = 0) : d292615 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291137, d292615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30697 q selected
    | true =>
      simp only [d291137, d292615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291138 q = 0) : d292616 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291138, d292616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291138, d292616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291139 q = 0) : d292617 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291139, d292617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291139, d292617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291160 q = 0) : d292638 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291160, d292638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291160, d292638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291161 q = 0) : d292639 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291161, d292639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291161, d292639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d291162 q = 0) : d292640 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291162, d292640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291162, d292640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro30702 (p : Pattern) (selected : d291164 p = 0) : d292642 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291150 q = 0) : d292628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291150, d292628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30665 q selected
    | true =>
      simp only [d291150, d292628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291151 q = 0) : d292629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291151, d292629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291151, d292629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291152 q = 0) : d292630 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291152, d292630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291152, d292630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291153 q = 0) : d292631 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291153, d292631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291153, d292631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291154 q = 0) : d292632 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291154, d292632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291154, d292632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291164 q = 0) : d292642 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291164, d292642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291164, d292642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30703 (p : Pattern) (selected : d291184 p = 0) : d292662 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291170 q = 0) : d292648 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291170, d292648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291170, d292648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30671 q selected
  have h2 (q : Pattern) (selected : d291022 q = 0) : d292559 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291022, d292559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30671 q selected
    | true =>
      simp only [d291022, d292559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291171 q = 0) : d292649 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291171, d292649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291171, d292649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291023 q = 0) : d292560 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291023, d292560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291023, d292560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291172 q = 0) : d292650 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291172, d292650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291172, d292650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291173 q = 0) : d292651 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291173, d292651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291173, d292651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291174 q = 0) : d292652 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291174, d292652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291174, d292652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30672 q selected
  have h8 (q : Pattern) (selected : d291028 q = 0) : d292565 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291028, d292565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30672 q selected
    | true =>
      simp only [d291028, d292565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291175 q = 0) : d292653 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291175, d292653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291175, d292653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291029 q = 0) : d292566 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291029, d292566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291029, d292566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291176 q = 0) : d292654 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291176, d292654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291176, d292654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291177 q = 0) : d292655 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291177, d292655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291177, d292655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291178 q = 0) : d292656 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291178, d292656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291178, d292656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291179 q = 0) : d292657 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291179, d292657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291179, d292657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30653 q selected
  have h15 (q : Pattern) (selected : d290937 q = 0) : d292474 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290937, d292474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30653 q selected
    | true =>
      simp only [d290937, d292474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d291180 q = 0) : d292658 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291180, d292658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d291180, d292658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d290938 q = 0) : d292475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290938, d292475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d290938, d292475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d291181 q = 0) : d292659 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291181, d292659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d291181, d292659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d291182 q = 0) : d292660 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291182, d292660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d291182, d292660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d291183 q = 0) : d292661 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291183, d292661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291183, d292661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d291184 q = 0) : d292662 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291184, d292662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291184, d292662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro30704 (p : Pattern) (selected : d291195 p = 0) : d292673 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291185 q = 0) : d292663 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291185, d292663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291185, d292663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30652 q selected
  have h2 (q : Pattern) (selected : d290931 q = 0) : d292468 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290931, d292468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30652 q selected
    | true =>
      simp only [d290931, d292468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291186 q = 0) : d292664 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291186, d292664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291186, d292664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290932 q = 0) : d292469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290932, d292469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290932, d292469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291187 q = 0) : d292665 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291187, d292665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291187, d292665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291188 q = 0) : d292666 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291188, d292666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291188, d292666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291179 q = 0) : d292657 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291179, d292657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291179, d292657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30653 q selected
  have h8 (q : Pattern) (selected : d290937 q = 0) : d292474 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290937, d292474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30653 q selected
    | true =>
      simp only [d290937, d292474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291180 q = 0) : d292658 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291180, d292658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291180, d292658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290938 q = 0) : d292475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290938, d292475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290938, d292475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291181 q = 0) : d292659 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291181, d292659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291181, d292659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291182 q = 0) : d292660 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291182, d292660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291182, d292660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291189 q = 0) : d292667 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291189, d292667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291189, d292667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291190 q = 0) : d292668 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291190, d292668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291190, d292668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30654 q selected
  have h15 (q : Pattern) (selected : d290944 q = 0) : d292481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290944, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30654 q selected
    | true =>
      simp only [d290944, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d291191 q = 0) : d292669 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291191, d292669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d291191, d292669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d290945 q = 0) : d292482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290945, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d290945, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d291192 q = 0) : d292670 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291192, d292670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d291192, d292670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d291193 q = 0) : d292671 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291193, d292671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d291193, d292671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d291194 q = 0) : d292672 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291194, d292672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291194, d292672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d291195 q = 0) : d292673 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291195, d292673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291195, d292673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro30705 (p : Pattern) (selected : d291200 p = 0) : d292678 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291179 q = 0) : d292657 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291179, d292657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291179, d292657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30653 q selected
  have h2 (q : Pattern) (selected : d290937 q = 0) : d292474 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290937, d292474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30653 q selected
    | true =>
      simp only [d290937, d292474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291180 q = 0) : d292658 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291180, d292658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291180, d292658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290938 q = 0) : d292475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290938, d292475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290938, d292475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291181 q = 0) : d292659 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291181, d292659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291181, d292659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291182 q = 0) : d292660 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291182, d292660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291182, d292660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291190 q = 0) : d292668 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291190, d292668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291190, d292668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30654 q selected
  have h8 (q : Pattern) (selected : d290944 q = 0) : d292481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290944, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30654 q selected
    | true =>
      simp only [d290944, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291191 q = 0) : d292669 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291191, d292669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291191, d292669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290945 q = 0) : d292482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290945, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290945, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291192 q = 0) : d292670 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291192, d292670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291192, d292670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291193 q = 0) : d292671 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291193, d292671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291193, d292671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291194 q = 0) : d292672 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291194, d292672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291194, d292672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291199 q = 0) : d292677 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291199, d292677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291199, d292677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d291200 q = 0) : d292678 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291200, d292678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291200, d292678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30706 (p : Pattern) (selected : d291210 p = 0) : d292688 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291205 q = 0) : d292683 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291205, d292683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291205, d292683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30656 q selected
  have h2 (q : Pattern) (selected : d290952 q = 0) : d292489 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290952, d292489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30656 q selected
    | true =>
      simp only [d290952, d292489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291206 q = 0) : d292684 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291206, d292684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291206, d292684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290953 q = 0) : d292490 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290953, d292490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290953, d292490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291207 q = 0) : d292685 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291207, d292685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291207, d292685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291208 q = 0) : d292686 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291208, d292686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291208, d292686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291190 q = 0) : d292668 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291190, d292668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291190, d292668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30654 q selected
  have h8 (q : Pattern) (selected : d290944 q = 0) : d292481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290944, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30654 q selected
    | true =>
      simp only [d290944, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291191 q = 0) : d292669 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291191, d292669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291191, d292669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290945 q = 0) : d292482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290945, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290945, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291192 q = 0) : d292670 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291192, d292670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291192, d292670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291193 q = 0) : d292671 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291193, d292671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291193, d292671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291209 q = 0) : d292687 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291209, d292687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291209, d292687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291199 q = 0) : d292677 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291199, d292677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291199, d292677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d291210 q = 0) : d292688 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291210, d292688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291210, d292688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30707 (p : Pattern) (selected : d291214 p = 0) : d292692 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291190 q = 0) : d292668 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291190, d292668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291190, d292668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30654 q selected
  have h2 (q : Pattern) (selected : d290944 q = 0) : d292481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290944, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30654 q selected
    | true =>
      simp only [d290944, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291191 q = 0) : d292669 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291191, d292669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291191, d292669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290945 q = 0) : d292482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290945, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290945, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291192 q = 0) : d292670 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291192, d292670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291192, d292670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291193 q = 0) : d292671 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291193, d292671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291193, d292671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291199 q = 0) : d292677 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291199, d292677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291199, d292677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291214 q = 0) : d292692 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291214, d292692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291214, d292692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30708 (p : Pattern) (selected : d291220 p = 0) : d292698 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291196 q = 0) : d292674 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291196, d292674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30703 q selected
    | true =>
      simp only [d291196, d292674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30704 q selected
  have h2 (q : Pattern) (selected : d291197 q = 0) : d292675 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291197, d292675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291197, d292675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291198 q = 0) : d292676 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291198, d292676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291198, d292676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291201 q = 0) : d292679 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291201, d292679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30704 q selected
    | true =>
      simp only [d291201, d292679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30705 q selected
  have h5 (q : Pattern) (selected : d291202 q = 0) : d292680 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291202, d292680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291202, d292680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291203 q = 0) : d292681 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291203, d292681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291203, d292681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291204 q = 0) : d292682 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291204, d292682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291204, d292682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291211 q = 0) : d292689 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291211, d292689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30704 q selected
    | true =>
      simp only [d291211, d292689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30706 q selected
  have h9 (q : Pattern) (selected : d291212 q = 0) : d292690 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291212, d292690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291212, d292690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291213 q = 0) : d292691 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291213, d292691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291213, d292691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291215 q = 0) : d292693 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291215, d292693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30706 q selected
    | true =>
      simp only [d291215, d292693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30707 q selected
  have h12 (q : Pattern) (selected : d291216 q = 0) : d292694 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291216, d292694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291216, d292694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d291217 q = 0) : d292695 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291217, d292695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291217, d292695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291218 q = 0) : d292696 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291218, d292696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291218, d292696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d291219 q = 0) : d292697 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291219, d292697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291219, d292697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d291220 q = 0) : d292698 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291220, d292698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d291220, d292698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro30709 (p : Pattern) (selected : d291225 p = 0) : d292703 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291211 q = 0) : d292689 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291211, d292689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30704 q selected
    | true =>
      simp only [d291211, d292689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30706 q selected
  have h2 (q : Pattern) (selected : d291212 q = 0) : d292690 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291212, d292690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291212, d292690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291213 q = 0) : d292691 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291213, d292691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291213, d292691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291215 q = 0) : d292693 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291215, d292693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30706 q selected
    | true =>
      simp only [d291215, d292693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30707 q selected
  have h5 (q : Pattern) (selected : d291216 q = 0) : d292694 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291216, d292694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291216, d292694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291217 q = 0) : d292695 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291217, d292695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291217, d292695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291218 q = 0) : d292696 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291218, d292696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291218, d292696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291223 q = 0) : d292701 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291223, d292701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291223, d292701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291224 q = 0) : d292702 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291224, d292702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291224, d292702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291225 q = 0) : d292703 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291225, d292703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291225, d292703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30710 (p : Pattern) (selected : d291231 p = 0) : d292709 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291221 q = 0) : d292699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291221, d292699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30708 q selected
    | true =>
      simp only [d291221, d292699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291222 q = 0) : d292700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291222, d292700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291222, d292700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291226 q = 0) : d292704 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291226, d292704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30709 q selected
    | true =>
      simp only [d291226, d292704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291227 q = 0) : d292705 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291227, d292705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291227, d292705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291228 q = 0) : d292706 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291228, d292706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291228, d292706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291229 q = 0) : d292707 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291229, d292707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291229, d292707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291230 q = 0) : d292708 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291230, d292708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291230, d292708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291231 q = 0) : d292709 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291231, d292709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291231, d292709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30711 (p : Pattern) (selected : d291233 p = 0) : d292711 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291215 q = 0) : d292693 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291215, d292693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30706 q selected
    | true =>
      simp only [d291215, d292693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30707 q selected
  have h2 (q : Pattern) (selected : d291216 q = 0) : d292694 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291216, d292694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291216, d292694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291217 q = 0) : d292695 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291217, d292695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291217, d292695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291223 q = 0) : d292701 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291223, d292701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291223, d292701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291232 q = 0) : d292710 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291232, d292710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291232, d292710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291233 q = 0) : d292711 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291233, d292711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291233, d292711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30712 (p : Pattern) (selected : d291239 p = 0) : d292717 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291226 q = 0) : d292704 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291226, d292704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30709 q selected
    | true =>
      simp only [d291226, d292704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291227 q = 0) : d292705 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291227, d292705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291227, d292705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291234 q = 0) : d292712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291234, d292712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30711 q selected
    | true =>
      simp only [d291234, d292712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291235 q = 0) : d292713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291235, d292713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291235, d292713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291236 q = 0) : d292714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291236, d292714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291236, d292714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291237 q = 0) : d292715 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291237, d292715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291237, d292715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291238 q = 0) : d292716 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291238, d292716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291238, d292716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291239 q = 0) : d292717 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291239, d292717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291239, d292717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30713 (p : Pattern) (selected : d291255 p = 0) : d292673 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291241 q = 0) : d292663 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291241, d292663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291241, d292663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30677 q selected
  have h2 (q : Pattern) (selected : d291054 q = 0) : d292468 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291054, d292468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30677 q selected
    | true =>
      simp only [d291054, d292468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291242 q = 0) : d292664 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291242, d292664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291242, d292664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291055 q = 0) : d292469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291055, d292469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291055, d292469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291243 q = 0) : d292665 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291243, d292665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291243, d292665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291244 q = 0) : d292666 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291244, d292666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291244, d292666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291245 q = 0) : d292657 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291245, d292657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291245, d292657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30678 q selected
  have h8 (q : Pattern) (selected : d291060 q = 0) : d292474 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291060, d292474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30678 q selected
    | true =>
      simp only [d291060, d292474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291246 q = 0) : d292658 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291246, d292658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291246, d292658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291061 q = 0) : d292475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291061, d292475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291061, d292475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291247 q = 0) : d292659 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291247, d292659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291247, d292659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291248 q = 0) : d292660 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291248, d292660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291248, d292660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291249 q = 0) : d292667 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291249, d292667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291249, d292667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291250 q = 0) : d292668 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291250, d292668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291250, d292668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30679 q selected
  have h15 (q : Pattern) (selected : d291067 q = 0) : d292481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291067, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30679 q selected
    | true =>
      simp only [d291067, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d291251 q = 0) : d292669 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291251, d292669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d291251, d292669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d291068 q = 0) : d292482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291068, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d291068, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d291252 q = 0) : d292670 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291252, d292670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d291252, d292670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d291253 q = 0) : d292671 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291253, d292671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d291253, d292671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d291254 q = 0) : d292672 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291254, d292672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291254, d292672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d291255 q = 0) : d292673 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291255, d292673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291255, d292673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro30714 (p : Pattern) (selected : d291262 p = 0) : d292688 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291256 q = 0) : d292683 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291256, d292683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291256, d292683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30681 q selected
  have h2 (q : Pattern) (selected : d291075 q = 0) : d292489 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291075, d292489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30681 q selected
    | true =>
      simp only [d291075, d292489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291257 q = 0) : d292684 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291257, d292684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291257, d292684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291076 q = 0) : d292490 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291076, d292490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291076, d292490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291258 q = 0) : d292685 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291258, d292685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291258, d292685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291259 q = 0) : d292686 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291259, d292686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291259, d292686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291250 q = 0) : d292668 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291250, d292668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291250, d292668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30679 q selected
  have h8 (q : Pattern) (selected : d291067 q = 0) : d292481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291067, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30679 q selected
    | true =>
      simp only [d291067, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291251 q = 0) : d292669 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291251, d292669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291251, d292669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291068 q = 0) : d292482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291068, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291068, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291252 q = 0) : d292670 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291252, d292670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291252, d292670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291253 q = 0) : d292671 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291253, d292671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291253, d292671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291260 q = 0) : d292687 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291260, d292687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291260, d292687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291261 q = 0) : d292677 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291261, d292677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291261, d292677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d291262 q = 0) : d292688 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291262, d292688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291262, d292688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30715 (p : Pattern) (selected : d291266 p = 0) : d292692 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291250 q = 0) : d292668 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291250, d292668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291250, d292668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30679 q selected
  have h2 (q : Pattern) (selected : d291067 q = 0) : d292481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291067, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30679 q selected
    | true =>
      simp only [d291067, d292481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291251 q = 0) : d292669 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291251, d292669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291251, d292669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291068 q = 0) : d292482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291068, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291068, d292482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291252 q = 0) : d292670 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291252, d292670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291252, d292670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291253 q = 0) : d292671 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291253, d292671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291253, d292671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291261 q = 0) : d292677 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291261, d292677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291261, d292677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291266 q = 0) : d292692 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291266, d292692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291266, d292692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30716 (p : Pattern) (selected : d291273 p = 0) : d292703 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291263 q = 0) : d292689 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291263, d292689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30713 q selected
    | true =>
      simp only [d291263, d292689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30714 q selected
  have h2 (q : Pattern) (selected : d291264 q = 0) : d292690 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291264, d292690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291264, d292690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291265 q = 0) : d292691 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291265, d292691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291265, d292691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291267 q = 0) : d292693 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291267, d292693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30714 q selected
    | true =>
      simp only [d291267, d292693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30715 q selected
  have h5 (q : Pattern) (selected : d291268 q = 0) : d292694 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291268, d292694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291268, d292694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291269 q = 0) : d292695 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291269, d292695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291269, d292695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291270 q = 0) : d292696 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291270, d292696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291270, d292696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291271 q = 0) : d292701 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291271, d292701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291271, d292701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291272 q = 0) : d292702 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291272, d292702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291272, d292702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291273 q = 0) : d292703 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291273, d292703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291273, d292703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30717 (p : Pattern) (selected : d291277 p = 0) : d292711 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291267 q = 0) : d292693 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291267, d292693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30714 q selected
    | true =>
      simp only [d291267, d292693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30715 q selected
  have h2 (q : Pattern) (selected : d291268 q = 0) : d292694 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291268, d292694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291268, d292694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291269 q = 0) : d292695 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291269, d292695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291269, d292695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291271 q = 0) : d292701 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291271, d292701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291271, d292701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291276 q = 0) : d292710 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291276, d292710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291276, d292710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291277 q = 0) : d292711 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291277, d292711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291277, d292711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30718 (p : Pattern) (selected : d291283 p = 0) : d292717 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291274 q = 0) : d292704 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291274, d292704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30716 q selected
    | true =>
      simp only [d291274, d292704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291275 q = 0) : d292705 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291275, d292705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291275, d292705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291278 q = 0) : d292712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291278, d292712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30717 q selected
    | true =>
      simp only [d291278, d292712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291279 q = 0) : d292713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291279, d292713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291279, d292713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291280 q = 0) : d292714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291280, d292714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291280, d292714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291281 q = 0) : d292715 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291281, d292715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291281, d292715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291282 q = 0) : d292716 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291282, d292716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291282, d292716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291283 q = 0) : d292717 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291283, d292717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291283, d292717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30719 (p : Pattern) (selected : d291287 p = 0) : d292722 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291278 q = 0) : d292712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291278, d292712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30717 q selected
    | true =>
      simp only [d291278, d292712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291279 q = 0) : d292713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291279, d292713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291279, d292713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291284 q = 0) : d292719 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291284, d292719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291284, d292719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291285 q = 0) : d292720 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291285, d292720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291285, d292720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291286 q = 0) : d292721 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291286, d292721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291286, d292721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291287 q = 0) : d292722 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291287, d292722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291287, d292722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30720 (p : Pattern) (selected : d291293 p = 0) : d292728 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291226 q = 0) : d292704 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291226, d292704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30709 q selected
    | true =>
      simp only [d291226, d292704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291227 q = 0) : d292705 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291227, d292705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291227, d292705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291290 q = 0) : d292725 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291290, d292725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291290, d292725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291291 q = 0) : d292726 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291291, d292726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291291, d292726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291292 q = 0) : d292727 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291292, d292727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291292, d292727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291293 q = 0) : d292728 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291293, d292728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291293, d292728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30721 (p : Pattern) (selected : d291299 p = 0) : d292734 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291240 q = 0) : d292718 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291240, d292718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30710 q selected
    | true =>
      simp only [d291240, d292718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30712 q selected
  have h2 (q : Pattern) (selected : d291288 q = 0) : d292723 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291288, d292723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30718 q selected
    | true =>
      simp only [d291288, d292723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30719 q selected
  have h3 (q : Pattern) (selected : d291289 q = 0) : d292724 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291289, d292724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291289, d292724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291294 q = 0) : d292729 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291294, d292729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30720 q selected
    | true =>
      simp only [d291294, d292729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291295 q = 0) : d292730 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291295, d292730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291295, d292730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291296 q = 0) : d292731 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291296, d292731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291296, d292731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291297 q = 0) : d292732 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291297, d292732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291297, d292732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291298 q = 0) : d292733 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291298, d292733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291298, d292733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d291299 q = 0) : d292734 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291299, d292734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291299, d292734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro30722 (p : Pattern) (selected : d291304 p = 0) : d292722 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291234 q = 0) : d292712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291234, d292712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30711 q selected
    | true =>
      simp only [d291234, d292712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291235 q = 0) : d292713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291235, d292713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291235, d292713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291301 q = 0) : d292719 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291301, d292719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291301, d292719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291302 q = 0) : d292720 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291302, d292720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291302, d292720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291303 q = 0) : d292721 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291303, d292721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291303, d292721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291304 q = 0) : d292722 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291304, d292722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291304, d292722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30723 (p : Pattern) (selected : d291310 p = 0) : d292741 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291305 q = 0) : d292736 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291305, d292736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30722 q selected
    | true =>
      simp only [d291305, d292736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291306 q = 0) : d292737 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291306, d292737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291306, d292737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291307 q = 0) : d292738 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291307, d292738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291307, d292738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291308 q = 0) : d292739 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291308, d292739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291308, d292739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291309 q = 0) : d292740 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291309, d292740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291309, d292740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291310 q = 0) : d292741 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291310, d292741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291310, d292741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30724 (p : Pattern) (selected : d291316 p = 0) : d292747 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d290990 q = 0) : d292527 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290990, d292527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290990, d292527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30663 q selected
  have h2 (q : Pattern) (selected : d290991 q = 0) : d292528 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290991, d292528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290991, d292528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291000 q = 0) : d292537 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291000, d292537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30663 q selected
    | true =>
      simp only [d291000, d292537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30666 q selected
  have h4 (q : Pattern) (selected : d291001 q = 0) : d292538 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d291001, d292538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291001, d292538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291002 q = 0) : d292539 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d291002, d292539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291002, d292539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291143 q = 0) : d292621 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291143, d292621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30689 q selected
    | true =>
      simp only [d291143, d292621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30698 q selected
  have h7 (q : Pattern) (selected : d291156 q = 0) : d292634 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291156, d292634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30699 q selected
    | true =>
      simp only [d291156, d292634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30700 q selected
  have h8 (q : Pattern) (selected : d291157 q = 0) : d292635 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d291157, d292635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291157, d292635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d291158 q = 0) : d292636 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d291158, d292636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291158, d292636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d291159 q = 0) : d292637 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d291159, d292637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291159, d292637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291163 q = 0) : d292641 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291163, d292641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291163, d292641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30701 q selected
  have h12 (q : Pattern) (selected : d291165 q = 0) : d292643 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291165, d292643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291165, d292643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30702 q selected
  have h13 (q : Pattern) (selected : d291166 q = 0) : d292644 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d291166, d292644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291166, d292644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291167 q = 0) : d292645 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d291167, d292645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291167, d292645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d291168 q = 0) : d292646 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d291168, d292646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d291168, d292646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d291169 q = 0) : d292647 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d291169, d292647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291169, d292647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d291300 q = 0) : d292735 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291300, d292735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291300, d292735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30721 q selected
  have h18 (q : Pattern) (selected : d291311 q = 0) : d292742 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291311, d292742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291311, d292742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30723 q selected
  have h19 (q : Pattern) (selected : d291312 q = 0) : d292743 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d291312, d292743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d291312, d292743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d291313 q = 0) : d292744 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d291313, d292744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d291313, d292744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d291314 q = 0) : d292745 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d291314, d292745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d291314, d292745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d291315 q = 0) : d292746 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d291315, d292746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d291315, d292746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d291316 q = 0) : d292747 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d291316, d292747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d291316, d292747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro30725 (p : Pattern) (selected : d291322 p = 0) : d292753 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291317 q = 0) : d292748 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d291317, d292748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291317, d292748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30724 q selected
  have h2 (q : Pattern) (selected : d291318 q = 0) : d292749 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d291318, d292749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291318, d292749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291319 q = 0) : d292750 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d291319, d292750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291319, d292750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291320 q = 0) : d292751 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d291320, d292751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291320, d292751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291321 q = 0) : d292752 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d291321, d292752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291321, d292752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291322 q = 0) : d292753 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d291322, d292753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291322, d292753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30726 (p : Pattern) (selected : d291327 p = 0) : d292758 p = 1 := by
  have h0 (q : Pattern) (selected : d1527 q = 0) : d52968 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro460 q selected
    | true =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro461 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1528 q = 0) : d52969 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro384 q selected
  have h3 (q : Pattern) (selected : d1529 q = 0) : d52970 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291326 q = 0) : d292757 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291326, d292757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291326, d292757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d291327 q = 0) : d292758 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291327, d292758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291327, d292758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro30727 (p : Pattern) (selected : d291333 p = 0) : d292764 p = 1 := by
  have h0 (q : Pattern) (selected : d1543 q = 0) : d52984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro463 q selected
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro464 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1544 q = 0) : d52985 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro385 q selected
  have h3 (q : Pattern) (selected : d1545 q = 0) : d52986 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291332 q = 0) : d292763 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291332, d292763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291332, d292763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d291333 q = 0) : d292764 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291333, d292764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291333, d292764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro30728 (p : Pattern) (selected : d291340 p = 0) : d292771 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1575 q = 0) : d53016 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro467 q selected
  have h2 (q : Pattern) (selected : d1115 q = 0) : d52696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
  have h3 (q : Pattern) (selected : d1576 q = 0) : d53017 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10129 q = 0) : d101556 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro467 q selected
    | true =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d19 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10130 q = 0) : d101557 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291339 q = 0) : d292770 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291339, d292770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291339, d292770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291340 q = 0) : d292771 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291340, d292771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291340, d292771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30729 (p : Pattern) (selected : d291346 p = 0) : d292777 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291328 q = 0) : d292759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291328, d292759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30726 q selected
    | true =>
      simp only [d291328, d292759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291329 q = 0) : d292760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291329, d292760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291329, d292760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291330 q = 0) : d292761 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291330, d292761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291330, d292761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291331 q = 0) : d292762 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291331, d292762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291331, d292762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291334 q = 0) : d292765 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291334, d292765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30727 q selected
    | true =>
      simp only [d291334, d292765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291335 q = 0) : d292766 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291335, d292766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291335, d292766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291336 q = 0) : d292767 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291336, d292767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291336, d292767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291337 q = 0) : d292768 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291337, d292768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291337, d292768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291338 q = 0) : d292769 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291338, d292769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291338, d292769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291341 q = 0) : d292772 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291341, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30728 q selected
    | true =>
      simp only [d291341, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291342 q = 0) : d292773 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291342, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291342, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d291343 q = 0) : d292774 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291343, d292774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291343, d292774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d291344 q = 0) : d292775 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291344, d292775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291344, d292775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d291345 q = 0) : d292776 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291345, d292776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291345, d292776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d291346 q = 0) : d292777 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291346, d292777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291346, d292777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30730 (p : Pattern) (selected : d291348 p = 0) : d292779 p = 1 := by
  have h0 (q : Pattern) (selected : d1543 q = 0) : d52984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro463 q selected
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro464 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1544 q = 0) : d52985 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro385 q selected
  have h3 (q : Pattern) (selected : d1545 q = 0) : d52986 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d25765 q = 0) : d199013 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25765, d199013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18806 q selected
    | true =>
      simp only [d25765, d199013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d25766 q = 0) : d199014 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25766, d199014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25766, d199014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d291347 q = 0) : d292778 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291347, d292778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291347, d292778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291348 q = 0) : d292779 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291348, d292779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291348, d292779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro30731 (p : Pattern) (selected : d291355 p = 0) : d292786 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291349 q = 0) : d292780 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291349, d292780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30730 q selected
    | true =>
      simp only [d291349, d292780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291350 q = 0) : d292781 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291350, d292781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291350, d292781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291351 q = 0) : d292782 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291351, d292782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291351, d292782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291352 q = 0) : d292783 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291352, d292783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291352, d292783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291341 q = 0) : d292772 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291341, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30728 q selected
    | true =>
      simp only [d291341, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291342 q = 0) : d292773 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291342, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291342, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291343 q = 0) : d292774 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291343, d292774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291343, d292774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291344 q = 0) : d292775 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291344, d292775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291344, d292775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291353 q = 0) : d292784 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291353, d292784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291353, d292784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291354 q = 0) : d292785 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291354, d292785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291354, d292785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291355 q = 0) : d292786 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291355, d292786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291355, d292786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30732 (p : Pattern) (selected : d291359 p = 0) : d292790 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291341 q = 0) : d292772 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291341, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30728 q selected
    | true =>
      simp only [d291341, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291342 q = 0) : d292773 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291342, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291342, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291343 q = 0) : d292774 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291343, d292774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291343, d292774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291344 q = 0) : d292775 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291344, d292775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291344, d292775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291354 q = 0) : d292785 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291354, d292785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291354, d292785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291359 q = 0) : d292790 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291359, d292790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291359, d292790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30733 (p : Pattern) (selected : d291366 p = 0) : d292797 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291356 q = 0) : d292787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291356, d292787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30729 q selected
    | true =>
      simp only [d291356, d292787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30731 q selected
  have h2 (q : Pattern) (selected : d291357 q = 0) : d292788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291357, d292788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291357, d292788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291358 q = 0) : d292789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291358, d292789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291358, d292789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291360 q = 0) : d292791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291360, d292791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30731 q selected
    | true =>
      simp only [d291360, d292791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30732 q selected
  have h5 (q : Pattern) (selected : d291361 q = 0) : d292792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291361, d292792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291361, d292792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291362 q = 0) : d292793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291362, d292793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291362, d292793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291363 q = 0) : d292794 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291363, d292794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291363, d292794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291364 q = 0) : d292795 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291364, d292795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291364, d292795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291365 q = 0) : d292796 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291365, d292796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291365, d292796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291366 q = 0) : d292797 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291366, d292797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291366, d292797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30734 (p : Pattern) (selected : d291370 p = 0) : d292801 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291360 q = 0) : d292791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291360, d292791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30731 q selected
    | true =>
      simp only [d291360, d292791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30732 q selected
  have h2 (q : Pattern) (selected : d291361 q = 0) : d292792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291361, d292792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291361, d292792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291362 q = 0) : d292793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291362, d292793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291362, d292793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291364 q = 0) : d292795 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291364, d292795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291364, d292795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291369 q = 0) : d292800 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291369, d292800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291369, d292800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291370 q = 0) : d292801 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291370, d292801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291370, d292801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30735 (p : Pattern) (selected : d291376 p = 0) : d292807 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291367 q = 0) : d292798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291367, d292798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30733 q selected
    | true =>
      simp only [d291367, d292798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291368 q = 0) : d292799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291368, d292799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291368, d292799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291371 q = 0) : d292802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30734 q selected
    | true =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291372 q = 0) : d292803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291373 q = 0) : d292804 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291373, d292804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291373, d292804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291374 q = 0) : d292805 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291374, d292805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291374, d292805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291375 q = 0) : d292806 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291375, d292806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291375, d292806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291376 q = 0) : d292807 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291376, d292807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291376, d292807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30736 (p : Pattern) (selected : d291380 p = 0) : d292811 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291371 q = 0) : d292802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30734 q selected
    | true =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291372 q = 0) : d292803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291377 q = 0) : d292808 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291377, d292808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291377, d292808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291378 q = 0) : d292809 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291378, d292809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291378, d292809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291379 q = 0) : d292810 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291379, d292810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291379, d292810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291380 q = 0) : d292811 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291380, d292811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291380, d292811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30737 (p : Pattern) (selected : d291386 p = 0) : d292817 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291381 q = 0) : d292812 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291381, d292812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30735 q selected
    | true =>
      simp only [d291381, d292812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30736 q selected
  have h2 (q : Pattern) (selected : d291382 q = 0) : d292813 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291382, d292813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291382, d292813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291383 q = 0) : d292814 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291383, d292814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291383, d292814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291384 q = 0) : d292815 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291384, d292815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291384, d292815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291385 q = 0) : d292816 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291385, d292816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291385, d292816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291386 q = 0) : d292817 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291386, d292817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291386, d292817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30738 (p : Pattern) (selected : d291389 p = 0) : d292820 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291367 q = 0) : d292798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291367, d292798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30733 q selected
    | true =>
      simp only [d291367, d292798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291368 q = 0) : d292799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291368, d292799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291368, d292799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291371 q = 0) : d292802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30734 q selected
    | true =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291372 q = 0) : d292803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291373 q = 0) : d292804 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291373, d292804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291373, d292804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291374 q = 0) : d292805 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291374, d292805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291374, d292805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291375 q = 0) : d292806 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291375, d292806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291375, d292806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291389 q = 0) : d292820 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291389, d292820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291389, d292820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30739 (p : Pattern) (selected : d291390 p = 0) : d292821 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291371 q = 0) : d292802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30734 q selected
    | true =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291372 q = 0) : d292803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291377 q = 0) : d292808 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291377, d292808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291377, d292808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291378 q = 0) : d292809 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291378, d292809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291378, d292809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291379 q = 0) : d292810 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291379, d292810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291379, d292810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291390 q = 0) : d292821 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291390, d292821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291390, d292821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30740 (p : Pattern) (selected : d291396 p = 0) : d292827 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291381 q = 0) : d292812 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291381, d292812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30735 q selected
    | true =>
      simp only [d291381, d292812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30736 q selected
  have h2 (q : Pattern) (selected : d291382 q = 0) : d292813 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291382, d292813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291382, d292813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291383 q = 0) : d292814 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291383, d292814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291383, d292814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291384 q = 0) : d292815 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291384, d292815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291384, d292815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291385 q = 0) : d292816 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291385, d292816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291385, d292816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291391 q = 0) : d292822 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291391, d292822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30738 q selected
    | true =>
      simp only [d291391, d292822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30739 q selected
  have h7 (q : Pattern) (selected : d291392 q = 0) : d292823 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291392, d292823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291392, d292823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291393 q = 0) : d292824 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291393, d292824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291393, d292824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291394 q = 0) : d292825 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291394, d292825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291394, d292825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291395 q = 0) : d292826 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291395, d292826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291395, d292826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291396 q = 0) : d292827 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291396, d292827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291396, d292827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30741 (p : Pattern) (selected : d291401 p = 0) : d292832 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291367 q = 0) : d292798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291367, d292798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30733 q selected
    | true =>
      simp only [d291367, d292798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291368 q = 0) : d292799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291368, d292799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291368, d292799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291371 q = 0) : d292802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30734 q selected
    | true =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291372 q = 0) : d292803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291373 q = 0) : d292804 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291373, d292804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291373, d292804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291374 q = 0) : d292805 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291374, d292805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291374, d292805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291400 q = 0) : d292831 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291400, d292831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291400, d292831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291401 q = 0) : d292832 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291401, d292832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291401, d292832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30742 (p : Pattern) (selected : d291403 p = 0) : d292834 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291371 q = 0) : d292802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30734 q selected
    | true =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291372 q = 0) : d292803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291377 q = 0) : d292808 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291377, d292808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291377, d292808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291378 q = 0) : d292809 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291378, d292809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291378, d292809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291402 q = 0) : d292833 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291402, d292833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291402, d292833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291403 q = 0) : d292834 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291403, d292834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291403, d292834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30743 (p : Pattern) (selected : d291410 p = 0) : d292841 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291367 q = 0) : d292798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291367, d292798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30733 q selected
    | true =>
      simp only [d291367, d292798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291368 q = 0) : d292799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291368, d292799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291368, d292799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291371 q = 0) : d292802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30734 q selected
    | true =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291372 q = 0) : d292803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291373 q = 0) : d292804 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291373, d292804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291373, d292804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291408 q = 0) : d292839 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291408, d292839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291408, d292839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291409 q = 0) : d292840 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291409, d292840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291409, d292840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291410 q = 0) : d292841 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291410, d292841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291410, d292841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30744 (p : Pattern) (selected : d291413 p = 0) : d292844 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291371 q = 0) : d292802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30734 q selected
    | true =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291372 q = 0) : d292803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291377 q = 0) : d292808 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291377, d292808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291377, d292808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291411 q = 0) : d292842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291411, d292842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291411, d292842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291412 q = 0) : d292843 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291412, d292843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291412, d292843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291413 q = 0) : d292844 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291413, d292844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291413, d292844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30745 (p : Pattern) (selected : d291418 p = 0) : d292849 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1200 q = 0) : d52781 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro405 q selected
    | true =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1201 q = 0) : d52782 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291417 q = 0) : d292848 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291417, d292848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291417, d292848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291418 q = 0) : d292849 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291418, d292849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291418, d292849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro30746 (p : Pattern) (selected : d291424 p = 0) : d292855 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291419 q = 0) : d292850 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291419, d292850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30745 q selected
    | true =>
      simp only [d291419, d292850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291420 q = 0) : d292851 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291420, d292851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291420, d292851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291421 q = 0) : d292852 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291421, d292852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291421, d292852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291422 q = 0) : d292853 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291422, d292853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291422, d292853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291328 q = 0) : d292759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291328, d292759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30726 q selected
    | true =>
      simp only [d291328, d292759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291329 q = 0) : d292760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291329, d292760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291329, d292760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291330 q = 0) : d292761 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291330, d292761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291330, d292761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291331 q = 0) : d292762 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291331, d292762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291331, d292762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291423 q = 0) : d292854 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291423, d292854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291423, d292854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291334 q = 0) : d292765 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291334, d292765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30727 q selected
    | true =>
      simp only [d291334, d292765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291335 q = 0) : d292766 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291335, d292766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291335, d292766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d291336 q = 0) : d292767 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291336, d292767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291336, d292767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d291337 q = 0) : d292768 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291337, d292768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291337, d292768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d291338 q = 0) : d292769 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291338, d292769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291338, d292769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d291424 q = 0) : d292855 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291424, d292855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291424, d292855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30747 (p : Pattern) (selected : d291428 p = 0) : d292859 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291334 q = 0) : d292765 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291334, d292765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30727 q selected
    | true =>
      simp only [d291334, d292765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291335 q = 0) : d292766 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291335, d292766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291335, d292766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291336 q = 0) : d292767 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291336, d292767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291336, d292767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291337 q = 0) : d292768 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291337, d292768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291337, d292768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291341 q = 0) : d292772 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291341, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30728 q selected
    | true =>
      simp only [d291341, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291342 q = 0) : d292773 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291342, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291342, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291343 q = 0) : d292774 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291343, d292774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291343, d292774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291344 q = 0) : d292775 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291344, d292775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291344, d292775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291345 q = 0) : d292776 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291345, d292776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291345, d292776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291354 q = 0) : d292785 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291354, d292785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291354, d292785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291428 q = 0) : d292859 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291428, d292859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291428, d292859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30748 (p : Pattern) (selected : d291434 p = 0) : d292865 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291425 q = 0) : d292856 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291425, d292856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30746 q selected
    | true =>
      simp only [d291425, d292856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30729 q selected
  have h2 (q : Pattern) (selected : d291426 q = 0) : d292857 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291426, d292857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291426, d292857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291427 q = 0) : d292858 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291427, d292858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291427, d292858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291429 q = 0) : d292860 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291429, d292860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30729 q selected
    | true =>
      simp only [d291429, d292860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30747 q selected
  have h5 (q : Pattern) (selected : d291430 q = 0) : d292861 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291430, d292861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291430, d292861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291431 q = 0) : d292862 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291431, d292862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291431, d292862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291432 q = 0) : d292863 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291432, d292863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291432, d292863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291356 q = 0) : d292787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291356, d292787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30729 q selected
    | true =>
      simp only [d291356, d292787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30731 q selected
  have h9 (q : Pattern) (selected : d291357 q = 0) : d292788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291357, d292788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291357, d292788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291358 q = 0) : d292789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291358, d292789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291358, d292789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291360 q = 0) : d292791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291360, d292791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30731 q selected
    | true =>
      simp only [d291360, d292791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30732 q selected
  have h12 (q : Pattern) (selected : d291361 q = 0) : d292792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291361, d292792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291361, d292792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d291362 q = 0) : d292793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291362, d292793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291362, d292793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291363 q = 0) : d292794 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291363, d292794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291363, d292794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d291433 q = 0) : d292864 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291433, d292864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291433, d292864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d291434 q = 0) : d292865 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291434, d292865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d291434, d292865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro30749 (p : Pattern) (selected : d291440 p = 0) : d292871 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291435 q = 0) : d292866 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291435, d292866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30748 q selected
    | true =>
      simp only [d291435, d292866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291436 q = 0) : d292867 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291436, d292867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291436, d292867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291367 q = 0) : d292798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291367, d292798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30733 q selected
    | true =>
      simp only [d291367, d292798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291368 q = 0) : d292799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291368, d292799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291368, d292799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291437 q = 0) : d292868 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291437, d292868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291437, d292868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291438 q = 0) : d292869 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291438, d292869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291438, d292869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291439 q = 0) : d292870 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291439, d292870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291439, d292870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291440 q = 0) : d292871 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291440, d292871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291440, d292871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
end NetHack.Soko22Hazard87
