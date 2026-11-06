import NetHack.Soko22Hazard87.EqIntroBlocks0132
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro33250 (p : Pattern) (selected : d46310 p = 0) : d319797 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46304 q = 0) : d319791 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46304, d319791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46304, d319791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33211 q selected
  have h2 (q : Pattern) (selected : d46070 q = 0) : d319667 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46070, d319667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33211 q selected
    | true =>
      simp only [d46070, d319667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46305 q = 0) : d319792 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46305, d319792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46305, d319792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46071 q = 0) : d319668 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46071, d319668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46071, d319668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46306 q = 0) : d319793 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46306, d319793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46306, d319793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46307 q = 0) : d319794 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46307, d319794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46307, d319794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46295 q = 0) : d319782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46295, d319782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46295, d319782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33188 q selected
  have h8 (q : Pattern) (selected : d45946 q = 0) : d319543 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45946, d319543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33188 q selected
    | true =>
      simp only [d45946, d319543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46296 q = 0) : d319783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46296, d319783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46296, d319783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45947 q = 0) : d319544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45947, d319544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d45947, d319544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46297 q = 0) : d319784 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46297, d319784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46297, d319784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d46298 q = 0) : d319785 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46298, d319785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46298, d319785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d46308 q = 0) : d319795 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46308, d319795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46308, d319795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46309 q = 0) : d319796 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46309, d319796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46309, d319796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46310 q = 0) : d319797 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46310, d319797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46310, d319797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro33251 (p : Pattern) (selected : d46324 p = 0) : d319811 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46315 q = 0) : d319802 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46315, d319802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46315, d319802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33190 q selected
  have h2 (q : Pattern) (selected : d45958 q = 0) : d319555 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45958, d319555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33190 q selected
    | true =>
      simp only [d45958, d319555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46316 q = 0) : d319803 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46316, d319803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46316, d319803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45959 q = 0) : d319556 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45959, d319556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45959, d319556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46317 q = 0) : d319804 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46317, d319804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46317, d319804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46318 q = 0) : d319805 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46318, d319805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46318, d319805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46319 q = 0) : d319806 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46319, d319806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46319, d319806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33191 q selected
  have h8 (q : Pattern) (selected : d45963 q = 0) : d319560 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45963, d319560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33191 q selected
    | true =>
      simp only [d45963, d319560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46320 q = 0) : d319807 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46320, d319807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46320, d319807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45964 q = 0) : d319561 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45964, d319561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d45964, d319561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46321 q = 0) : d319808 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46321, d319808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46321, d319808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d46322 q = 0) : d319809 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46322, d319809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46322, d319809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d46323 q = 0) : d319810 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46323, d319810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46323, d319810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46295 q = 0) : d319782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46295, d319782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46295, d319782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33188 q selected
  have h15 (q : Pattern) (selected : d45946 q = 0) : d319543 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45946, d319543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33188 q selected
    | true =>
      simp only [d45946, d319543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d46296 q = 0) : d319783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46296, d319783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d46296, d319783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d45947 q = 0) : d319544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45947, d319544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d45947, d319544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d46297 q = 0) : d319784 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46297, d319784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d46297, d319784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d46298 q = 0) : d319785 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46298, d319785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d46298, d319785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d46309 q = 0) : d319796 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46309, d319796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d46309, d319796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d46324 q = 0) : d319811 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46324, d319811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46324, d319811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro33252 (p : Pattern) (selected : d46329 p = 0) : d319816 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46319 q = 0) : d319806 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46319, d319806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46319, d319806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33191 q selected
  have h2 (q : Pattern) (selected : d45963 q = 0) : d319560 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45963, d319560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33191 q selected
    | true =>
      simp only [d45963, d319560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46320 q = 0) : d319807 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46320, d319807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46320, d319807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45964 q = 0) : d319561 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45964, d319561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45964, d319561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46321 q = 0) : d319808 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46321, d319808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46321, d319808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46322 q = 0) : d319809 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46322, d319809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46322, d319809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46328 q = 0) : d319815 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46328, d319815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46328, d319815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15019 q = 0) : d123144 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6680 q selected
  have h9 (q : Pattern) (selected : d9844 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6680 q selected
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15020 q = 0) : d123145 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, d123145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15020, d123145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d9846 q = 0) : d101367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15021 q = 0) : d123146 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15021, d123146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15021, d123146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15022 q = 0) : d123147 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15022, d123147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15022, d123147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15023 q = 0) : d123148 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15023, d123148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15023, d123148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46329 q = 0) : d319816 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46329, d319816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46329, d319816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro33253 (p : Pattern) (selected : d46335 p = 0) : d319822 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46301 q = 0) : d319788 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46301, d319788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33248 q selected
    | true =>
      simp only [d46301, d319788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33249 q selected
  have h2 (q : Pattern) (selected : d46302 q = 0) : d319789 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46302, d319789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46302, d319789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46303 q = 0) : d319790 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46303, d319790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46303, d319790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46311 q = 0) : d319798 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46311, d319798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33249 q selected
    | true =>
      simp only [d46311, d319798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33250 q selected
  have h5 (q : Pattern) (selected : d46312 q = 0) : d319799 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46312, d319799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46312, d319799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46313 q = 0) : d319800 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46313, d319800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46313, d319800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46314 q = 0) : d319801 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46314, d319801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46314, d319801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46325 q = 0) : d319812 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46325, d319812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33249 q selected
    | true =>
      simp only [d46325, d319812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33251 q selected
  have h9 (q : Pattern) (selected : d46326 q = 0) : d319813 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46326, d319813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46326, d319813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46327 q = 0) : d319814 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46327, d319814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46327, d319814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46330 q = 0) : d319817 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46330, d319817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33251 q selected
    | true =>
      simp only [d46330, d319817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33252 q selected
  have h12 (q : Pattern) (selected : d46331 q = 0) : d319818 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46331, d319818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46331, d319818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46332 q = 0) : d319819 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46332, d319819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46332, d319819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46333 q = 0) : d319820 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46333, d319820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46333, d319820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d46334 q = 0) : d319821 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46334, d319821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46334, d319821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d46335 q = 0) : d319822 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46335, d319822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d46335, d319822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro33254 (p : Pattern) (selected : d46340 p = 0) : d319827 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46325 q = 0) : d319812 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46325, d319812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33249 q selected
    | true =>
      simp only [d46325, d319812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33251 q selected
  have h2 (q : Pattern) (selected : d46326 q = 0) : d319813 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46326, d319813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46326, d319813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46327 q = 0) : d319814 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46327, d319814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46327, d319814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46330 q = 0) : d319817 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46330, d319817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33251 q selected
    | true =>
      simp only [d46330, d319817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33252 q selected
  have h5 (q : Pattern) (selected : d46331 q = 0) : d319818 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46331, d319818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46331, d319818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46332 q = 0) : d319819 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46332, d319819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46332, d319819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46333 q = 0) : d319820 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46333, d319820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46333, d319820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46338 q = 0) : d319825 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46338, d319825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46338, d319825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46339 q = 0) : d319826 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46339, d319826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46339, d319826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46340 q = 0) : d319827 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46340, d319827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46340, d319827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro33255 (p : Pattern) (selected : d46346 p = 0) : d319833 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46336 q = 0) : d319823 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46336, d319823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33253 q selected
    | true =>
      simp only [d46336, d319823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46337 q = 0) : d319824 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46337, d319824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46337, d319824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46341 q = 0) : d319828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46341, d319828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33254 q selected
    | true =>
      simp only [d46341, d319828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46342 q = 0) : d319829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46342, d319829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46342, d319829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46343 q = 0) : d319830 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46343, d319830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46343, d319830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46344 q = 0) : d319831 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46344, d319831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46344, d319831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46345 q = 0) : d319832 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46345, d319832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46345, d319832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46346 q = 0) : d319833 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46346, d319833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46346, d319833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33256 (p : Pattern) (selected : d46348 p = 0) : d319835 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46330 q = 0) : d319817 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46330, d319817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33251 q selected
    | true =>
      simp only [d46330, d319817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33252 q selected
  have h2 (q : Pattern) (selected : d46331 q = 0) : d319818 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46331, d319818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46331, d319818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46332 q = 0) : d319819 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46332, d319819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46332, d319819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46338 q = 0) : d319825 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46338, d319825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46338, d319825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46347 q = 0) : d319834 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46347, d319834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46347, d319834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46348 q = 0) : d319835 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46348, d319835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46348, d319835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33257 (p : Pattern) (selected : d46354 p = 0) : d319841 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46341 q = 0) : d319828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46341, d319828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33254 q selected
    | true =>
      simp only [d46341, d319828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46342 q = 0) : d319829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46342, d319829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46342, d319829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46349 q = 0) : d319836 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46349, d319836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33256 q selected
    | true =>
      simp only [d46349, d319836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46350 q = 0) : d319837 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46350, d319837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46350, d319837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46351 q = 0) : d319838 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46351, d319838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46351, d319838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46352 q = 0) : d319839 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46352, d319839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46352, d319839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46353 q = 0) : d319840 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46353, d319840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46353, d319840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46354 q = 0) : d319841 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46354, d319841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46354, d319841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33258 (p : Pattern) (selected : d46374 p = 0) : d319787 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46356 q = 0) : d319773 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46356, d319773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46356, d319773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33217 q selected
  have h2 (q : Pattern) (selected : d46109 q = 0) : d319513 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46109, d319513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33217 q selected
    | true =>
      simp only [d46109, d319513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46357 q = 0) : d319774 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46357, d319774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46357, d319774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46110 q = 0) : d319514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46110, d319514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46110, d319514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46358 q = 0) : d319775 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46358, d319775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46358, d319775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46359 q = 0) : d319776 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46359, d319776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46359, d319776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46360 q = 0) : d319777 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46360, d319777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46360, d319777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33219 q selected
  have h8 (q : Pattern) (selected : d46125 q = 0) : d319525 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46125, d319525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33219 q selected
    | true =>
      simp only [d46125, d319525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46361 q = 0) : d319778 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46361, d319778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46361, d319778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46126 q = 0) : d319526 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46126, d319526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46126, d319526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46362 q = 0) : d319779 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46362, d319779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46362, d319779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d46363 q = 0) : d319780 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46363, d319780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46363, d319780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d46364 q = 0) : d319781 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46364, d319781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46364, d319781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46365 q = 0) : d319767 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46365, d319767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46365, d319767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33220 q selected
  have h15 (q : Pattern) (selected : d46136 q = 0) : d319534 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46136, d319534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33220 q selected
    | true =>
      simp only [d46136, d319534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d46366 q = 0) : d319768 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46366, d319768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d46366, d319768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d46137 q = 0) : d319535 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46137, d319535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d46137, d319535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d46367 q = 0) : d319769 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46367, d319769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d46367, d319769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d46368 q = 0) : d319770 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46368, d319770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d46368, d319770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d46369 q = 0) : d319782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46369, d319782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46369, d319782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33221 q selected
  have h21 (q : Pattern) (selected : d46145 q = 0) : d319543 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46145, d319543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33221 q selected
    | true =>
      simp only [d46145, d319543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d46370 q = 0) : d319783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46370, d319783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d46370, d319783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d46146 q = 0) : d319544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46146, d319544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d46146, d319544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d46371 q = 0) : d319784 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46371, d319784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d46371, d319784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d46372 q = 0) : d319785 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46372, d319785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d46372, d319785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d46373 q = 0) : d319786 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46373, d319786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d46373, d319786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d46374 q = 0) : d319787 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46374, d319787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46374, d319787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro33259 (p : Pattern) (selected : d46385 p = 0) : d319811 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46375 q = 0) : d319802 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46375, d319802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46375, d319802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33223 q selected
  have h2 (q : Pattern) (selected : d46157 q = 0) : d319555 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46157, d319555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33223 q selected
    | true =>
      simp only [d46157, d319555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46376 q = 0) : d319803 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46376, d319803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46376, d319803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46158 q = 0) : d319556 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46158, d319556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46158, d319556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46377 q = 0) : d319804 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46377, d319804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46377, d319804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46378 q = 0) : d319805 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46378, d319805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46378, d319805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46379 q = 0) : d319806 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46379, d319806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46379, d319806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33224 q selected
  have h8 (q : Pattern) (selected : d46162 q = 0) : d319560 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46162, d319560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33224 q selected
    | true =>
      simp only [d46162, d319560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46380 q = 0) : d319807 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46380, d319807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46380, d319807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46163 q = 0) : d319561 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46163, d319561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46163, d319561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46381 q = 0) : d319808 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46381, d319808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46381, d319808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d46382 q = 0) : d319809 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46382, d319809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46382, d319809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d46383 q = 0) : d319810 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46383, d319810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46383, d319810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46369 q = 0) : d319782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46369, d319782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46369, d319782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33221 q selected
  have h15 (q : Pattern) (selected : d46145 q = 0) : d319543 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46145, d319543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33221 q selected
    | true =>
      simp only [d46145, d319543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d46370 q = 0) : d319783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46370, d319783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d46370, d319783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d46146 q = 0) : d319544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46146, d319544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d46146, d319544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d46371 q = 0) : d319784 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46371, d319784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d46371, d319784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d46372 q = 0) : d319785 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46372, d319785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d46372, d319785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d46384 q = 0) : d319796 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46384, d319796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d46384, d319796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d46385 q = 0) : d319811 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46385, d319811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46385, d319811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro33260 (p : Pattern) (selected : d46390 p = 0) : d319816 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46379 q = 0) : d319806 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46379, d319806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46379, d319806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33224 q selected
  have h2 (q : Pattern) (selected : d46162 q = 0) : d319560 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46162, d319560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33224 q selected
    | true =>
      simp only [d46162, d319560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46380 q = 0) : d319807 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46380, d319807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46380, d319807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46163 q = 0) : d319561 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46163, d319561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46163, d319561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46381 q = 0) : d319808 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46381, d319808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46381, d319808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46382 q = 0) : d319809 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46382, d319809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46382, d319809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46389 q = 0) : d319815 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46389, d319815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46389, d319815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15073 q = 0) : d123144 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15073, d123144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15073, d123144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6696 q selected
  have h9 (q : Pattern) (selected : d9952 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6696 q selected
    | true =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15074 q = 0) : d123145 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15074, d123145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15074, d123145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d9954 q = 0) : d101367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9954, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9954, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d15075 q = 0) : d123146 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15075, d123146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15075, d123146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15076 q = 0) : d123147 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15076, d123147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15076, d123147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15077 q = 0) : d123148 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15077, d123148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d15077, d123148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46390 q = 0) : d319816 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46390, d319816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46390, d319816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro33261 (p : Pattern) (selected : d46397 p = 0) : d319827 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46386 q = 0) : d319812 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46386, d319812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33258 q selected
    | true =>
      simp only [d46386, d319812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33259 q selected
  have h2 (q : Pattern) (selected : d46387 q = 0) : d319813 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46387, d319813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46387, d319813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46388 q = 0) : d319814 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46388, d319814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46388, d319814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46391 q = 0) : d319817 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46391, d319817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33259 q selected
    | true =>
      simp only [d46391, d319817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33260 q selected
  have h5 (q : Pattern) (selected : d46392 q = 0) : d319818 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46392, d319818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46392, d319818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46393 q = 0) : d319819 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46393, d319819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46393, d319819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46394 q = 0) : d319820 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46394, d319820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46394, d319820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46395 q = 0) : d319825 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46395, d319825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46395, d319825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46396 q = 0) : d319826 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46396, d319826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46396, d319826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46397 q = 0) : d319827 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46397, d319827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46397, d319827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro33262 (p : Pattern) (selected : d46401 p = 0) : d319835 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46391 q = 0) : d319817 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46391, d319817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33259 q selected
    | true =>
      simp only [d46391, d319817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33260 q selected
  have h2 (q : Pattern) (selected : d46392 q = 0) : d319818 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46392, d319818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46392, d319818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46393 q = 0) : d319819 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46393, d319819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46393, d319819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46395 q = 0) : d319825 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46395, d319825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46395, d319825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46400 q = 0) : d319834 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46400, d319834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46400, d319834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46401 q = 0) : d319835 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46401, d319835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46401, d319835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33263 (p : Pattern) (selected : d46407 p = 0) : d319841 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46398 q = 0) : d319828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46398, d319828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33261 q selected
    | true =>
      simp only [d46398, d319828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46399 q = 0) : d319829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46399, d319829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46399, d319829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46402 q = 0) : d319836 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46402, d319836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33262 q selected
    | true =>
      simp only [d46402, d319836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46403 q = 0) : d319837 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46403, d319837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46403, d319837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46404 q = 0) : d319838 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46404, d319838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46404, d319838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46405 q = 0) : d319839 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46405, d319839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46405, d319839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46406 q = 0) : d319840 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46406, d319840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46406, d319840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46407 q = 0) : d319841 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46407, d319841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46407, d319841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33264 (p : Pattern) (selected : d46411 p = 0) : d319846 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46402 q = 0) : d319836 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46402, d319836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33262 q selected
    | true =>
      simp only [d46402, d319836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46403 q = 0) : d319837 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46403, d319837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46403, d319837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46408 q = 0) : d319843 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46408, d319843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46408, d319843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46409 q = 0) : d319844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46409, d319844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46409, d319844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46410 q = 0) : d319845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46410, d319845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46410, d319845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46411 q = 0) : d319846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46411, d319846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46411, d319846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33265 (p : Pattern) (selected : d46414 p = 0) : d319849 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46319 q = 0) : d319806 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46319, d319806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46319, d319806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33191 q selected
  have h2 (q : Pattern) (selected : d45963 q = 0) : d319560 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45963, d319560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33191 q selected
    | true =>
      simp only [d45963, d319560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46320 q = 0) : d319807 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46320, d319807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46320, d319807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45964 q = 0) : d319561 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45964, d319561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45964, d319561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46321 q = 0) : d319808 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46321, d319808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46321, d319808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46322 q = 0) : d319809 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46322, d319809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46322, d319809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46328 q = 0) : d319815 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46328, d319815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46328, d319815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46414 q = 0) : d319849 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46414, d319849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46414, d319849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33266 (p : Pattern) (selected : d46420 p = 0) : d319855 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46325 q = 0) : d319812 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46325, d319812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33249 q selected
    | true =>
      simp only [d46325, d319812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33251 q selected
  have h2 (q : Pattern) (selected : d46326 q = 0) : d319813 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46326, d319813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46326, d319813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46327 q = 0) : d319814 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46327, d319814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46327, d319814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46330 q = 0) : d319817 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46330, d319817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33251 q selected
    | true =>
      simp only [d46330, d319817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33252 q selected
  have h5 (q : Pattern) (selected : d46331 q = 0) : d319818 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46331, d319818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46331, d319818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46332 q = 0) : d319819 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46332, d319819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46332, d319819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46333 q = 0) : d319820 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46333, d319820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46333, d319820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46415 q = 0) : d319850 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46415, d319850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33251 q selected
    | true =>
      simp only [d46415, d319850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33265 q selected
  have h9 (q : Pattern) (selected : d46416 q = 0) : d319851 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46416, d319851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46416, d319851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46417 q = 0) : d319852 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46417, d319852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46417, d319852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46418 q = 0) : d319853 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46418, d319853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46418, d319853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d46419 q = 0) : d319854 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46419, d319854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46419, d319854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46420 q = 0) : d319855 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46420, d319855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46420, d319855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro33267 (p : Pattern) (selected : d46426 p = 0) : d319861 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46421 q = 0) : d319856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46421, d319856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33266 q selected
    | true =>
      simp only [d46421, d319856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46422 q = 0) : d319857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46422, d319857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46422, d319857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46423 q = 0) : d319858 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46423, d319858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46423, d319858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46424 q = 0) : d319859 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46424, d319859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46424, d319859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46425 q = 0) : d319860 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46425, d319860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46425, d319860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46426 q = 0) : d319861 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46426, d319861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46426, d319861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33268 (p : Pattern) (selected : d46432 p = 0) : d319867 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46355 q = 0) : d319842 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46355, d319842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33255 q selected
    | true =>
      simp only [d46355, d319842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33257 q selected
  have h2 (q : Pattern) (selected : d46412 q = 0) : d319847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46412, d319847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33263 q selected
    | true =>
      simp only [d46412, d319847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33264 q selected
  have h3 (q : Pattern) (selected : d46413 q = 0) : d319848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46413, d319848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46413, d319848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46427 q = 0) : d319862 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46427, d319862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33267 q selected
    | true =>
      simp only [d46427, d319862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46428 q = 0) : d319863 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46428, d319863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46428, d319863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46429 q = 0) : d319864 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46429, d319864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46429, d319864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46430 q = 0) : d319865 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46430, d319865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46430, d319865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46431 q = 0) : d319866 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46431, d319866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46431, d319866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46432 q = 0) : d319867 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46432, d319867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46432, d319867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro33269 (p : Pattern) (selected : d46437 p = 0) : d319846 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46349 q = 0) : d319836 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46349, d319836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33256 q selected
    | true =>
      simp only [d46349, d319836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46350 q = 0) : d319837 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46350, d319837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46350, d319837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46434 q = 0) : d319843 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46434, d319843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46434, d319843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46435 q = 0) : d319844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46435, d319844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46435, d319844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46436 q = 0) : d319845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46436, d319845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46436, d319845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46437 q = 0) : d319846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46437, d319846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46437, d319846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33270 (p : Pattern) (selected : d46443 p = 0) : d319874 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46438 q = 0) : d319869 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46438, d319869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33269 q selected
    | true =>
      simp only [d46438, d319869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46439 q = 0) : d319870 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46439, d319870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46439, d319870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46440 q = 0) : d319871 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46440, d319871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46440, d319871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46441 q = 0) : d319872 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46441, d319872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46441, d319872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46442 q = 0) : d319873 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46442, d319873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46442, d319873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46443 q = 0) : d319874 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46443, d319874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46443, d319874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33271 (p : Pattern) (selected : d46449 p = 0) : d319880 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46002 q = 0) : d319599 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46002, d319599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46002, d319599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33198 q selected
  have h2 (q : Pattern) (selected : d46003 q = 0) : d319600 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46003, d319600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46003, d319600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46012 q = 0) : d319609 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46012, d319609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33198 q selected
    | true =>
      simp only [d46012, d319609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33201 q selected
  have h4 (q : Pattern) (selected : d46013 q = 0) : d319610 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46013, d319610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46013, d319610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46014 q = 0) : d319611 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46014, d319611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46014, d319611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46240 q = 0) : d319727 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46240, d319727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33234 q selected
    | true =>
      simp only [d46240, d319727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33243 q selected
  have h7 (q : Pattern) (selected : d46253 q = 0) : d319740 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46253, d319740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33244 q selected
    | true =>
      simp only [d46253, d319740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33245 q selected
  have h8 (q : Pattern) (selected : d46254 q = 0) : d319741 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46254, d319741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46254, d319741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46255 q = 0) : d319742 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46255, d319742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46255, d319742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46256 q = 0) : d319743 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d46256, d319743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46256, d319743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46260 q = 0) : d319747 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46260, d319747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46260, d319747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33246 q selected
  have h12 (q : Pattern) (selected : d46262 q = 0) : d319749 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46262, d319749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46262, d319749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33247 q selected
  have h13 (q : Pattern) (selected : d46263 q = 0) : d319750 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46263, d319750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46263, d319750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46264 q = 0) : d319751 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46264, d319751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46264, d319751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46265 q = 0) : d319752 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d46265, d319752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d46265, d319752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d46266 q = 0) : d319753 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d46266, d319753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46266, d319753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d46433 q = 0) : d319868 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46433, d319868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46433, d319868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33268 q selected
  have h18 (q : Pattern) (selected : d46444 q = 0) : d319875 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46444, d319875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46444, d319875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33270 q selected
  have h19 (q : Pattern) (selected : d46445 q = 0) : d319876 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46445, d319876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d46445, d319876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d46446 q = 0) : d319877 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46446, d319877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d46446, d319877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d46447 q = 0) : d319878 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d46447, d319878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d46447, d319878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d46448 q = 0) : d319879 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d46448, d319879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d46448, d319879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d46449 q = 0) : d319880 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d46449, d319880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d46449, d319880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro33272 (p : Pattern) (selected : d46455 p = 0) : d319886 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46450 q = 0) : d319881 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d46450, d319881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46450, d319881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33271 q selected
  have h2 (q : Pattern) (selected : d46451 q = 0) : d319882 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d46451, d319882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46451, d319882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46452 q = 0) : d319883 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d46452, d319883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46452, d319883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46453 q = 0) : d319884 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d46453, d319884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46453, d319884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46454 q = 0) : d319885 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d46454, d319885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46454, d319885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46455 q = 0) : d319886 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d46455, d319886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46455, d319886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33273 (p : Pattern) (selected : d46460 p = 0) : d319891 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d13 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14 q = 0) : d51866 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1084 q = 0) : d52665 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, d52665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1084, d52665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44996 q = 0) : d318841 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d44996, d318841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44996, d318841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46459 q = 0) : d319890 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46459, d319890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46459, d319890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46460 q = 0) : d319891 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46460, d319891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46460, d319891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro33274 (p : Pattern) (selected : d46466 p = 0) : d319897 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46461 q = 0) : d319892 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46461, d319892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46461, d319892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33273 q selected
  have h2 (q : Pattern) (selected : d32155 q = 0) : d242968 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6671 q selected
  have h3 (q : Pattern) (selected : d46462 q = 0) : d319893 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46462, d319893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46462, d319893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46463 q = 0) : d319894 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46463, d319894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46463, d319894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46464 q = 0) : d319895 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46464, d319895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46464, d319895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46465 q = 0) : d319896 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46465, d319896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46465, d319896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46466 q = 0) : d319897 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46466, d319897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46466, d319897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro33275 (p : Pattern) (selected : d46473 p = 0) : d319904 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d13 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14 q = 0) : d51866 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d15 q = 0) : d51867 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45587 q = 0) : d319302 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d45587, d319302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45587, d319302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46472 q = 0) : d319903 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46472, d319903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46472, d319903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46473 q = 0) : d319904 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46473, d319904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46473, d319904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro33276 (p : Pattern) (selected : d46482 p = 0) : d319913 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46461 q = 0) : d319892 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46461, d319892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46461, d319892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33273 q selected
  have h2 (q : Pattern) (selected : d32155 q = 0) : d242968 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6671 q selected
  have h3 (q : Pattern) (selected : d46462 q = 0) : d319893 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46462, d319893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46462, d319893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46463 q = 0) : d319894 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46463, d319894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46463, d319894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46464 q = 0) : d319895 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46464, d319895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46464, d319895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46465 q = 0) : d319896 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46465, d319896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46465, d319896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46474 q = 0) : d319905 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46474, d319905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46474, d319905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33275 q selected
  have h8 (q : Pattern) (selected : d1115 q = 0) : d52696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
  have h9 (q : Pattern) (selected : d46475 q = 0) : d319906 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46475, d319906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46475, d319906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46476 q = 0) : d319907 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46476, d319907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46476, d319907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46477 q = 0) : d319908 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46477, d319908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33275 q selected
    | true =>
      simp only [d46477, d319908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d19 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d46478 q = 0) : d319909 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46478, d319909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46478, d319909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46479 q = 0) : d319910 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46479, d319910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46479, d319910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46480 q = 0) : d319911 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46480, d319911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46480, d319911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d46481 q = 0) : d319912 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46481, d319912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d46481, d319912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d46482 q = 0) : d319913 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46482, d319913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46482, d319913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro33277 (p : Pattern) (selected : d46488 p = 0) : d319919 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46467 q = 0) : d319898 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33274 q selected
    | true =>
      simp only [d46467, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46468 q = 0) : d319899 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46468, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46469 q = 0) : d319900 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46469, d319900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46469, d319900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46470 q = 0) : d319901 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46470, d319901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46470, d319901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46471 q = 0) : d319902 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46471, d319902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46471, d319902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46483 q = 0) : d319914 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33276 q selected
    | true =>
      simp only [d46483, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46484 q = 0) : d319915 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46484, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46485 q = 0) : d319916 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46485, d319916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46485, d319916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46486 q = 0) : d319917 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46486, d319917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46486, d319917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46487 q = 0) : d319918 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46487, d319918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46487, d319918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46488 q = 0) : d319919 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46488, d319919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46488, d319919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro33278 (p : Pattern) (selected : d46490 p = 0) : d319921 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46467 q = 0) : d319898 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33274 q selected
    | true =>
      simp only [d46467, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46468 q = 0) : d319899 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46468, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46469 q = 0) : d319900 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46469, d319900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46469, d319900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46470 q = 0) : d319901 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46470, d319901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46470, d319901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46483 q = 0) : d319914 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33276 q selected
    | true =>
      simp only [d46483, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46484 q = 0) : d319915 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46484, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46485 q = 0) : d319916 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46485, d319916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46485, d319916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46486 q = 0) : d319917 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46486, d319917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46486, d319917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46487 q = 0) : d319918 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46487, d319918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46487, d319918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46489 q = 0) : d319920 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46489, d319920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46489, d319920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46490 q = 0) : d319921 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46490, d319921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46490, d319921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro33279 (p : Pattern) (selected : d46494 p = 0) : d319925 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46474 q = 0) : d319905 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46474, d319905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46474, d319905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33275 q selected
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
  have h3 (q : Pattern) (selected : d46475 q = 0) : d319906 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46475, d319906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46475, d319906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46476 q = 0) : d319907 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46476, d319907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46476, d319907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46477 q = 0) : d319908 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46477, d319908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33275 q selected
    | true =>
      simp only [d46477, d319908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d19 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46478 q = 0) : d319909 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46478, d319909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46478, d319909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46479 q = 0) : d319910 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46479, d319910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46479, d319910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46480 q = 0) : d319911 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46480, d319911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46480, d319911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46481 q = 0) : d319912 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46481, d319912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46481, d319912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46494 q = 0) : d319925 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46494, d319925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46494, d319925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h11 p selected
theorem eqIntro33280 (p : Pattern) (selected : d46500 p = 0) : d319931 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46483 q = 0) : d319914 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33276 q selected
    | true =>
      simp only [d46483, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46484 q = 0) : d319915 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46484, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46485 q = 0) : d319916 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46485, d319916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46485, d319916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46486 q = 0) : d319917 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46486, d319917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46486, d319917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46489 q = 0) : d319920 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46489, d319920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46489, d319920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46495 q = 0) : d319926 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46495, d319926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33279 q selected
    | true =>
      simp only [d46495, d319926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46496 q = 0) : d319927 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46496, d319927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46496, d319927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46497 q = 0) : d319928 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46497, d319928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46497, d319928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46498 q = 0) : d319929 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46498, d319929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46498, d319929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46499 q = 0) : d319930 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46499, d319930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46499, d319930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46500 q = 0) : d319931 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46500, d319931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46500, d319931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro33281 (p : Pattern) (selected : d46507 p = 0) : d319938 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46491 q = 0) : d319922 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46491, d319922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33277 q selected
    | true =>
      simp only [d46491, d319922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33278 q selected
  have h2 (q : Pattern) (selected : d46492 q = 0) : d319923 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46492, d319923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46492, d319923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46493 q = 0) : d319924 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46493, d319924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46493, d319924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46501 q = 0) : d319932 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46501, d319932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33278 q selected
    | true =>
      simp only [d46501, d319932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33280 q selected
  have h5 (q : Pattern) (selected : d46502 q = 0) : d319933 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46502, d319933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46502, d319933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46503 q = 0) : d319934 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46503, d319934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46503, d319934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46504 q = 0) : d319935 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46504, d319935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46504, d319935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46505 q = 0) : d319936 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46505, d319936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46505, d319936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46506 q = 0) : d319937 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46506, d319937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46506, d319937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46507 q = 0) : d319938 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46507, d319938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46507, d319938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro33282 (p : Pattern) (selected : d46511 p = 0) : d319942 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46501 q = 0) : d319932 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46501, d319932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33278 q selected
    | true =>
      simp only [d46501, d319932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33280 q selected
  have h2 (q : Pattern) (selected : d46502 q = 0) : d319933 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46502, d319933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46502, d319933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46503 q = 0) : d319934 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46503, d319934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46503, d319934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46505 q = 0) : d319936 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46505, d319936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46505, d319936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46510 q = 0) : d319941 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46510, d319941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46510, d319941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46511 q = 0) : d319942 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46511, d319942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46511, d319942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33283 (p : Pattern) (selected : d46517 p = 0) : d319948 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46508 q = 0) : d319939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, d319939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33281 q selected
    | true =>
      simp only [d46508, d319939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46509 q = 0) : d319940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, d319940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46509, d319940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46512 q = 0) : d319943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33282 q selected
    | true =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46513 q = 0) : d319944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46514 q = 0) : d319945 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, d319945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46514, d319945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46515 q = 0) : d319946 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46515, d319946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46515, d319946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46516 q = 0) : d319947 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46516, d319947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46516, d319947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46517 q = 0) : d319948 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46517, d319948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46517, d319948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33284 (p : Pattern) (selected : d46521 p = 0) : d319952 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46512 q = 0) : d319943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33282 q selected
    | true =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46513 q = 0) : d319944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46518 q = 0) : d319949 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, d319949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46518, d319949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46519 q = 0) : d319950 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46519, d319950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46519, d319950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46520 q = 0) : d319951 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46520, d319951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46520, d319951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46521 q = 0) : d319952 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46521, d319952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46521, d319952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33285 (p : Pattern) (selected : d46527 p = 0) : d319958 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46522 q = 0) : d319953 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46522, d319953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33283 q selected
    | true =>
      simp only [d46522, d319953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33284 q selected
  have h2 (q : Pattern) (selected : d46523 q = 0) : d319954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, d319954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46523, d319954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46524 q = 0) : d319955 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, d319955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46524, d319955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46525 q = 0) : d319956 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, d319956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46525, d319956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46526 q = 0) : d319957 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, d319957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46526, d319957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46527 q = 0) : d319958 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46527, d319958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46527, d319958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33286 (p : Pattern) (selected : d46530 p = 0) : d319961 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46508 q = 0) : d319939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, d319939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33281 q selected
    | true =>
      simp only [d46508, d319939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46509 q = 0) : d319940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, d319940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46509, d319940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46512 q = 0) : d319943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33282 q selected
    | true =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46513 q = 0) : d319944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46514 q = 0) : d319945 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, d319945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46514, d319945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46515 q = 0) : d319946 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46515, d319946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46515, d319946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46516 q = 0) : d319947 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46516, d319947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46516, d319947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46530 q = 0) : d319961 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46530, d319961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46530, d319961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33287 (p : Pattern) (selected : d46531 p = 0) : d319962 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46512 q = 0) : d319943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33282 q selected
    | true =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46513 q = 0) : d319944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46518 q = 0) : d319949 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, d319949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46518, d319949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46519 q = 0) : d319950 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46519, d319950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46519, d319950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46520 q = 0) : d319951 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46520, d319951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46520, d319951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46531 q = 0) : d319962 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46531, d319962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46531, d319962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33288 (p : Pattern) (selected : d46537 p = 0) : d319968 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46522 q = 0) : d319953 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46522, d319953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33283 q selected
    | true =>
      simp only [d46522, d319953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33284 q selected
  have h2 (q : Pattern) (selected : d46523 q = 0) : d319954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, d319954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46523, d319954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46524 q = 0) : d319955 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, d319955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46524, d319955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46525 q = 0) : d319956 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, d319956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46525, d319956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46526 q = 0) : d319957 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, d319957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46526, d319957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46532 q = 0) : d319963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46532, d319963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33286 q selected
    | true =>
      simp only [d46532, d319963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33287 q selected
  have h7 (q : Pattern) (selected : d46533 q = 0) : d319964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46533, d319964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46533, d319964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46534 q = 0) : d319965 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46534, d319965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46534, d319965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46535 q = 0) : d319966 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46535, d319966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46535, d319966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46536 q = 0) : d319967 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46536, d319967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46536, d319967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46537 q = 0) : d319968 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46537, d319968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46537, d319968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro33289 (p : Pattern) (selected : d46542 p = 0) : d319973 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46508 q = 0) : d319939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, d319939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33281 q selected
    | true =>
      simp only [d46508, d319939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46509 q = 0) : d319940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, d319940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46509, d319940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46512 q = 0) : d319943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33282 q selected
    | true =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46513 q = 0) : d319944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46514 q = 0) : d319945 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, d319945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46514, d319945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46515 q = 0) : d319946 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46515, d319946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46515, d319946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46541 q = 0) : d319972 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46541, d319972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46541, d319972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46542 q = 0) : d319973 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46542, d319973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46542, d319973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33290 (p : Pattern) (selected : d46544 p = 0) : d319975 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46512 q = 0) : d319943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33282 q selected
    | true =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46513 q = 0) : d319944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46518 q = 0) : d319949 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, d319949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46518, d319949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46519 q = 0) : d319950 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46519, d319950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46519, d319950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46543 q = 0) : d319974 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46543, d319974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46543, d319974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46544 q = 0) : d319975 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46544, d319975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46544, d319975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33291 (p : Pattern) (selected : d46551 p = 0) : d319982 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46508 q = 0) : d319939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, d319939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33281 q selected
    | true =>
      simp only [d46508, d319939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46509 q = 0) : d319940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, d319940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46509, d319940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46512 q = 0) : d319943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33282 q selected
    | true =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46513 q = 0) : d319944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46514 q = 0) : d319945 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, d319945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46514, d319945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46549 q = 0) : d319980 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46549, d319980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46549, d319980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46550 q = 0) : d319981 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46550, d319981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46550, d319981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46551 q = 0) : d319982 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46551, d319982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46551, d319982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33292 (p : Pattern) (selected : d46554 p = 0) : d319985 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46512 q = 0) : d319943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33282 q selected
    | true =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46513 q = 0) : d319944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46518 q = 0) : d319949 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, d319949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46518, d319949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46552 q = 0) : d319983 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46552, d319983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46552, d319983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46553 q = 0) : d319984 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46553, d319984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46553, d319984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46554 q = 0) : d319985 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46554, d319985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46554, d319985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33293 (p : Pattern) (selected : d46558 p = 0) : d319989 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46467 q = 0) : d319898 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33274 q selected
    | true =>
      simp only [d46467, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46468 q = 0) : d319899 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46468, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46469 q = 0) : d319900 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46469, d319900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46469, d319900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46470 q = 0) : d319901 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46470, d319901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46470, d319901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46471 q = 0) : d319902 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46471, d319902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46471, d319902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46558 q = 0) : d319989 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46558, d319989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46558, d319989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33294 (p : Pattern) (selected : d46564 p = 0) : d319995 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46559 q = 0) : d319990 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46559, d319990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33293 q selected
    | true =>
      simp only [d46559, d319990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33277 q selected
  have h2 (q : Pattern) (selected : d46560 q = 0) : d319991 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46560, d319991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46560, d319991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46561 q = 0) : d319992 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46561, d319992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46561, d319992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46491 q = 0) : d319922 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46491, d319922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33277 q selected
    | true =>
      simp only [d46491, d319922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33278 q selected
  have h5 (q : Pattern) (selected : d46492 q = 0) : d319923 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46492, d319923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46492, d319923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46493 q = 0) : d319924 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46493, d319924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46493, d319924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46562 q = 0) : d319993 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46562, d319993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46562, d319993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46501 q = 0) : d319932 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46501, d319932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33278 q selected
    | true =>
      simp only [d46501, d319932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33280 q selected
  have h9 (q : Pattern) (selected : d46502 q = 0) : d319933 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46502, d319933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46502, d319933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46503 q = 0) : d319934 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46503, d319934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46503, d319934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46504 q = 0) : d319935 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46504, d319935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46504, d319935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d46563 q = 0) : d319994 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46563, d319994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46563, d319994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46564 q = 0) : d319995 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46564, d319995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46564, d319995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro33295 (p : Pattern) (selected : d46570 p = 0) : d320001 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46565 q = 0) : d319996 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46565, d319996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33294 q selected
    | true =>
      simp only [d46565, d319996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46566 q = 0) : d319997 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46566, d319997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46566, d319997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46508 q = 0) : d319939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, d319939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33281 q selected
    | true =>
      simp only [d46508, d319939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46509 q = 0) : d319940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, d319940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46509, d319940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46567 q = 0) : d319998 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46567, d319998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46567, d319998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46568 q = 0) : d319999 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46568, d319999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46568, d319999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46569 q = 0) : d320000 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46569, d320000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46569, d320000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46570 q = 0) : d320001 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46570, d320001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46570, d320001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33296 (p : Pattern) (selected : d46573 p = 0) : d319891 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d158 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d159 q = 0) : d51866 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d159, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1233 q = 0) : d52665 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1233, d52665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1233, d52665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d45277 q = 0) : d318841 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d45277, d318841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45277, d318841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46572 q = 0) : d319890 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46572, d319890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46572, d319890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46573 q = 0) : d319891 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46573, d319891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46573, d319891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro33297 (p : Pattern) (selected : d46579 p = 0) : d319897 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46574 q = 0) : d319892 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46574, d319892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46574, d319892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33296 q selected
  have h2 (q : Pattern) (selected : d32325 q = 0) : d242968 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32325, d242968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32325, d242968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6689 q selected
  have h3 (q : Pattern) (selected : d46575 q = 0) : d319893 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46575, d319893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46575, d319893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46576 q = 0) : d319894 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46576, d319894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46576, d319894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46577 q = 0) : d319895 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46577, d319895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46577, d319895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46578 q = 0) : d319896 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46578, d319896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46578, d319896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46579 q = 0) : d319897 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46579, d319897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46579, d319897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro33298 (p : Pattern) (selected : d46586 p = 0) : d319904 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d158 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d159 q = 0) : d51866 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d159, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d160 q = 0) : d51867 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d160, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d160, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46115 q = 0) : d319302 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d46115, d319302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46115, d319302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46585 q = 0) : d319903 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46585, d319903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46585, d319903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46586 q = 0) : d319904 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46586, d319904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46586, d319904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro33299 (p : Pattern) (selected : d46595 p = 0) : d319913 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46574 q = 0) : d319892 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46574, d319892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46574, d319892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33296 q selected
  have h2 (q : Pattern) (selected : d32325 q = 0) : d242968 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32325, d242968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32325, d242968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6689 q selected
  have h3 (q : Pattern) (selected : d46575 q = 0) : d319893 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46575, d319893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46575, d319893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46576 q = 0) : d319894 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46576, d319894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46576, d319894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46577 q = 0) : d319895 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46577, d319895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46577, d319895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46578 q = 0) : d319896 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46578, d319896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46578, d319896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46587 q = 0) : d319905 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46587, d319905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46587, d319905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33298 q selected
  have h8 (q : Pattern) (selected : d1270 q = 0) : d52696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
  have h9 (q : Pattern) (selected : d46588 q = 0) : d319906 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46588, d319906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46588, d319906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46589 q = 0) : d319907 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46589, d319907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46589, d319907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46590 q = 0) : d319908 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46590, d319908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33298 q selected
    | true =>
      simp only [d46590, d319908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d46591 q = 0) : d319909 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46591, d319909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46591, d319909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46592 q = 0) : d319910 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46592, d319910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46592, d319910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46593 q = 0) : d319911 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46593, d319911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46593, d319911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d46594 q = 0) : d319912 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46594, d319912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d46594, d319912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d46595 q = 0) : d319913 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46595, d319913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46595, d319913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro33300 (p : Pattern) (selected : d46601 p = 0) : d319919 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46580 q = 0) : d319898 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46580, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33297 q selected
    | true =>
      simp only [d46580, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46581 q = 0) : d319899 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46581, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46581, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46582 q = 0) : d319900 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46582, d319900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46582, d319900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46583 q = 0) : d319901 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46583, d319901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46583, d319901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46584 q = 0) : d319902 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46584, d319902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46584, d319902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46596 q = 0) : d319914 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46596, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33299 q selected
    | true =>
      simp only [d46596, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46597 q = 0) : d319915 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46597, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46597, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46598 q = 0) : d319916 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46598, d319916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46598, d319916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46599 q = 0) : d319917 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46599, d319917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46599, d319917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46600 q = 0) : d319918 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46600, d319918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46600, d319918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46601 q = 0) : d319919 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46601, d319919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46601, d319919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro33301 (p : Pattern) (selected : d46603 p = 0) : d319921 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46580 q = 0) : d319898 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46580, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33297 q selected
    | true =>
      simp only [d46580, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46581 q = 0) : d319899 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46581, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46581, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46582 q = 0) : d319900 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46582, d319900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46582, d319900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46583 q = 0) : d319901 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46583, d319901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46583, d319901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46596 q = 0) : d319914 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46596, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33299 q selected
    | true =>
      simp only [d46596, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46597 q = 0) : d319915 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46597, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46597, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46598 q = 0) : d319916 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46598, d319916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46598, d319916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46599 q = 0) : d319917 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46599, d319917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46599, d319917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46600 q = 0) : d319918 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46600, d319918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46600, d319918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46602 q = 0) : d319920 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46602, d319920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46602, d319920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46603 q = 0) : d319921 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46603, d319921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46603, d319921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro33302 (p : Pattern) (selected : d46607 p = 0) : d319925 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46587 q = 0) : d319905 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46587, d319905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46587, d319905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33298 q selected
  have h2 (q : Pattern) (selected : d1270 q = 0) : d52696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
  have h3 (q : Pattern) (selected : d46588 q = 0) : d319906 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46588, d319906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46588, d319906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46589 q = 0) : d319907 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46589, d319907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46589, d319907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46590 q = 0) : d319908 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46590, d319908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33298 q selected
    | true =>
      simp only [d46590, d319908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46591 q = 0) : d319909 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46591, d319909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46591, d319909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46592 q = 0) : d319910 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46592, d319910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46592, d319910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46593 q = 0) : d319911 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46593, d319911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46593, d319911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46594 q = 0) : d319912 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46594, d319912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46594, d319912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46607 q = 0) : d319925 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46607, d319925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46607, d319925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h11 p selected
theorem eqIntro33303 (p : Pattern) (selected : d46613 p = 0) : d319931 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46596 q = 0) : d319914 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46596, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33299 q selected
    | true =>
      simp only [d46596, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46597 q = 0) : d319915 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46597, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46597, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46598 q = 0) : d319916 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46598, d319916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46598, d319916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46599 q = 0) : d319917 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46599, d319917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46599, d319917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46602 q = 0) : d319920 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46602, d319920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46602, d319920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46608 q = 0) : d319926 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46608, d319926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33302 q selected
    | true =>
      simp only [d46608, d319926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46609 q = 0) : d319927 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46609, d319927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46609, d319927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46610 q = 0) : d319928 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46610, d319928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46610, d319928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46611 q = 0) : d319929 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46611, d319929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46611, d319929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46612 q = 0) : d319930 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46612, d319930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46612, d319930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46613 q = 0) : d319931 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46613, d319931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46613, d319931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro33304 (p : Pattern) (selected : d46620 p = 0) : d319938 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46604 q = 0) : d319922 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46604, d319922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33300 q selected
    | true =>
      simp only [d46604, d319922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33301 q selected
  have h2 (q : Pattern) (selected : d46605 q = 0) : d319923 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46605, d319923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46605, d319923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46606 q = 0) : d319924 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46606, d319924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46606, d319924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46614 q = 0) : d319932 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46614, d319932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33301 q selected
    | true =>
      simp only [d46614, d319932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33303 q selected
  have h5 (q : Pattern) (selected : d46615 q = 0) : d319933 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46615, d319933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46615, d319933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46616 q = 0) : d319934 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46616, d319934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46616, d319934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46617 q = 0) : d319935 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46617, d319935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46617, d319935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46618 q = 0) : d319936 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46618, d319936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46618, d319936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46619 q = 0) : d319937 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46619, d319937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46619, d319937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46620 q = 0) : d319938 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46620, d319938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46620, d319938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro33305 (p : Pattern) (selected : d46624 p = 0) : d319942 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46614 q = 0) : d319932 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46614, d319932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33301 q selected
    | true =>
      simp only [d46614, d319932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33303 q selected
  have h2 (q : Pattern) (selected : d46615 q = 0) : d319933 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46615, d319933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46615, d319933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46616 q = 0) : d319934 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46616, d319934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46616, d319934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46618 q = 0) : d319936 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46618, d319936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46618, d319936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46623 q = 0) : d319941 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46623, d319941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46623, d319941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46624 q = 0) : d319942 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46624, d319942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46624, d319942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33306 (p : Pattern) (selected : d46630 p = 0) : d319948 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46621 q = 0) : d319939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46621, d319939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33304 q selected
    | true =>
      simp only [d46621, d319939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46622 q = 0) : d319940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46622, d319940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46622, d319940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46625 q = 0) : d319943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46625, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33305 q selected
    | true =>
      simp only [d46625, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46626 q = 0) : d319944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46626, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46626, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46627 q = 0) : d319945 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46627, d319945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46627, d319945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46628 q = 0) : d319946 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46628, d319946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46628, d319946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46629 q = 0) : d319947 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46629, d319947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46629, d319947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46630 q = 0) : d319948 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46630, d319948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46630, d319948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33307 (p : Pattern) (selected : d46634 p = 0) : d319952 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46625 q = 0) : d319943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46625, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33305 q selected
    | true =>
      simp only [d46625, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46626 q = 0) : d319944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46626, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46626, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46631 q = 0) : d319949 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46631, d319949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46631, d319949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46632 q = 0) : d319950 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46632, d319950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46632, d319950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46633 q = 0) : d319951 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46633, d319951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46633, d319951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46634 q = 0) : d319952 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46634, d319952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46634, d319952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33308 (p : Pattern) (selected : d46637 p = 0) : d320004 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46461 q = 0) : d319892 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46461, d319892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46461, d319892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33273 q selected
  have h2 (q : Pattern) (selected : d32155 q = 0) : d242968 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6671 q selected
  have h3 (q : Pattern) (selected : d46462 q = 0) : d319893 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46462, d319893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46462, d319893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46463 q = 0) : d319894 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46463, d319894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46463, d319894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46464 q = 0) : d319895 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46464, d319895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46464, d319895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46465 q = 0) : d319896 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46465, d319896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46465, d319896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46637 q = 0) : d320004 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46637, d320004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46637, d320004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro33309 (p : Pattern) (selected : d46643 p = 0) : d320010 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46467 q = 0) : d319898 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33274 q selected
    | true =>
      simp only [d46467, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46468 q = 0) : d319899 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46468, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46469 q = 0) : d319900 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46469, d319900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46469, d319900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46470 q = 0) : d319901 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46470, d319901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46470, d319901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46483 q = 0) : d319914 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33276 q selected
    | true =>
      simp only [d46483, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46484 q = 0) : d319915 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46484, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46485 q = 0) : d319916 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46485, d319916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46485, d319916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46486 q = 0) : d319917 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46486, d319917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46486, d319917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46487 q = 0) : d319918 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46487, d319918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46487, d319918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46638 q = 0) : d320005 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46638, d320005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33308 q selected
    | true =>
      simp only [d46638, d320005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46639 q = 0) : d320006 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46639, d320006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46639, d320006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d46640 q = 0) : d320007 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46640, d320007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46640, d320007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46641 q = 0) : d320008 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46641, d320008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46641, d320008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d46642 q = 0) : d320009 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46642, d320009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46642, d320009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46643 q = 0) : d320010 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46643, d320010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46643, d320010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro33310 (p : Pattern) (selected : d46644 p = 0) : d320011 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46638 q = 0) : d320005 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46638, d320005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33308 q selected
    | true =>
      simp only [d46638, d320005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46639 q = 0) : d320006 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46639, d320006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46639, d320006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46640 q = 0) : d320007 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46640, d320007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46640, d320007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46641 q = 0) : d320008 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46641, d320008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46641, d320008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46642 q = 0) : d320009 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46642, d320009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46642, d320009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46644 q = 0) : d320011 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46644, d320011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46644, d320011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33311 (p : Pattern) (selected : d46650 p = 0) : d320017 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46491 q = 0) : d319922 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46491, d319922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33277 q selected
    | true =>
      simp only [d46491, d319922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33278 q selected
  have h2 (q : Pattern) (selected : d46492 q = 0) : d319923 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46492, d319923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46492, d319923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46493 q = 0) : d319924 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46493, d319924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46493, d319924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46501 q = 0) : d319932 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46501, d319932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33278 q selected
    | true =>
      simp only [d46501, d319932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33280 q selected
  have h5 (q : Pattern) (selected : d46502 q = 0) : d319933 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46502, d319933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46502, d319933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46503 q = 0) : d319934 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46503, d319934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46503, d319934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46504 q = 0) : d319935 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46504, d319935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46504, d319935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46645 q = 0) : d320012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46645, d320012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33309 q selected
    | true =>
      simp only [d46645, d320012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33310 q selected
  have h9 (q : Pattern) (selected : d46646 q = 0) : d320013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46646, d320013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46646, d320013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46647 q = 0) : d320014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46647, d320014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46647, d320014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46648 q = 0) : d320015 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46648, d320015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46648, d320015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d46649 q = 0) : d320016 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46649, d320016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46649, d320016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46650 q = 0) : d320017 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46650, d320017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46650, d320017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro33312 (p : Pattern) (selected : d46656 p = 0) : d320023 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46651 q = 0) : d320018 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46651, d320018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33311 q selected
    | true =>
      simp only [d46651, d320018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46652 q = 0) : d320019 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46652, d320019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46652, d320019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46653 q = 0) : d320020 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46653, d320020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46653, d320020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46654 q = 0) : d320021 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46654, d320021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46654, d320021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46655 q = 0) : d320022 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46655, d320022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46655, d320022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46656 q = 0) : d320023 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46656, d320023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46656, d320023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33313 (p : Pattern) (selected : d46662 p = 0) : d320029 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46545 q = 0) : d319976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46545, d319976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33289 q selected
    | true =>
      simp only [d46545, d319976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33290 q selected
  have h2 (q : Pattern) (selected : d46546 q = 0) : d319977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46546, d319977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46546, d319977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46547 q = 0) : d319978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46547, d319978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46547, d319978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46548 q = 0) : d319979 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46548, d319979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46548, d319979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46555 q = 0) : d319986 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46555, d319986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33291 q selected
    | true =>
      simp only [d46555, d319986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33292 q selected
  have h6 (q : Pattern) (selected : d46556 q = 0) : d319987 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46556, d319987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46556, d319987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46557 q = 0) : d319988 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46557, d319988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46557, d319988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46571 q = 0) : d320002 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46571, d320002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33295 q selected
    | true =>
      simp only [d46571, d320002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33283 q selected
  have h9 (q : Pattern) (selected : d46635 q = 0) : d319953 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46635, d319953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33306 q selected
    | true =>
      simp only [d46635, d319953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33307 q selected
  have h10 (q : Pattern) (selected : d46636 q = 0) : d320003 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46636, d320003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46636, d320003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46657 q = 0) : d320024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46657, d320024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33312 q selected
    | true =>
      simp only [d46657, d320024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d46658 q = 0) : d320025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46658, d320025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46658, d320025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d46659 q = 0) : d320026 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46659, d320026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46659, d320026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46660 q = 0) : d320027 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46660, d320027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46660, d320027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d46661 q = 0) : d320028 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46661, d320028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46661, d320028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d46662 q = 0) : d320029 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46662, d320029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46662, d320029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro33314 (p : Pattern) (selected : d46663 p = 0) : d320030 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46508 q = 0) : d319939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, d319939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33281 q selected
    | true =>
      simp only [d46508, d319939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46509 q = 0) : d319940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, d319940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46509, d319940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46512 q = 0) : d319943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33282 q selected
    | true =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46513 q = 0) : d319944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46514 q = 0) : d319945 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, d319945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46514, d319945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46515 q = 0) : d319946 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46515, d319946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46515, d319946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46541 q = 0) : d319972 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46541, d319972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46541, d319972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46663 q = 0) : d320030 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46663, d320030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46663, d320030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33315 (p : Pattern) (selected : d46664 p = 0) : d320031 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46512 q = 0) : d319943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33282 q selected
    | true =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46513 q = 0) : d319944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46518 q = 0) : d319949 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, d319949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46518, d319949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46519 q = 0) : d319950 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46519, d319950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46519, d319950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46543 q = 0) : d319974 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46543, d319974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46543, d319974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46664 q = 0) : d320031 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46664, d320031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46664, d320031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33316 (p : Pattern) (selected : d46669 p = 0) : d320036 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46508 q = 0) : d319939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, d319939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33281 q selected
    | true =>
      simp only [d46508, d319939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46509 q = 0) : d319940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, d319940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46509, d319940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46512 q = 0) : d319943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33282 q selected
    | true =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46513 q = 0) : d319944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46514 q = 0) : d319945 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, d319945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46514, d319945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46549 q = 0) : d319980 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46549, d319980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46549, d319980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46550 q = 0) : d319981 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46550, d319981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46550, d319981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46669 q = 0) : d320036 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46669, d320036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46669, d320036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33317 (p : Pattern) (selected : d46670 p = 0) : d320037 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46512 q = 0) : d319943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33282 q selected
    | true =>
      simp only [d46512, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46513 q = 0) : d319944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46513, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46518 q = 0) : d319949 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, d319949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46518, d319949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46552 q = 0) : d319983 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46552, d319983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46552, d319983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46553 q = 0) : d319984 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46553, d319984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46553, d319984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46670 q = 0) : d320037 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46670, d320037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46670, d320037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33318 (p : Pattern) (selected : d46674 p = 0) : d320041 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46565 q = 0) : d319996 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46565, d319996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33294 q selected
    | true =>
      simp only [d46565, d319996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46566 q = 0) : d319997 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46566, d319997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46566, d319997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46508 q = 0) : d319939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, d319939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33281 q selected
    | true =>
      simp only [d46508, d319939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46509 q = 0) : d319940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, d319940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46509, d319940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46567 q = 0) : d319998 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46567, d319998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46567, d319998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46568 q = 0) : d319999 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46568, d319999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46568, d319999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46569 q = 0) : d320000 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46569, d320000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46569, d320000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46674 q = 0) : d320041 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46674, d320041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46674, d320041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33319 (p : Pattern) (selected : d46676 p = 0) : d319961 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46621 q = 0) : d319939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46621, d319939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33304 q selected
    | true =>
      simp only [d46621, d319939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46622 q = 0) : d319940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46622, d319940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46622, d319940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46625 q = 0) : d319943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46625, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33305 q selected
    | true =>
      simp only [d46625, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46626 q = 0) : d319944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46626, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46626, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46627 q = 0) : d319945 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46627, d319945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46627, d319945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46628 q = 0) : d319946 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46628, d319946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46628, d319946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46629 q = 0) : d319947 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46629, d319947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46629, d319947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46676 q = 0) : d319961 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46676, d319961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46676, d319961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33320 (p : Pattern) (selected : d46677 p = 0) : d319962 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46625 q = 0) : d319943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46625, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33305 q selected
    | true =>
      simp only [d46625, d319943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46626 q = 0) : d319944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46626, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46626, d319944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46631 q = 0) : d319949 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46631, d319949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46631, d319949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46632 q = 0) : d319950 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46632, d319950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46632, d319950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46633 q = 0) : d319951 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46633, d319951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46633, d319951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46677 q = 0) : d319962 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46677, d319962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46677, d319962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33321 (p : Pattern) (selected : d46680 p = 0) : d320044 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46651 q = 0) : d320018 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46651, d320018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33311 q selected
    | true =>
      simp only [d46651, d320018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46652 q = 0) : d320019 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46652, d320019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46652, d320019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46653 q = 0) : d320020 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46653, d320020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46653, d320020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46654 q = 0) : d320021 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46654, d320021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46654, d320021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46655 q = 0) : d320022 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46655, d320022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46655, d320022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46680 q = 0) : d320044 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46680, d320044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46680, d320044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33322 (p : Pattern) (selected : d46686 p = 0) : d320050 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46545 q = 0) : d319976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46545, d319976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33289 q selected
    | true =>
      simp only [d46545, d319976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33290 q selected
  have h2 (q : Pattern) (selected : d46546 q = 0) : d319977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46546, d319977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46546, d319977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46547 q = 0) : d319978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46547, d319978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46547, d319978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46548 q = 0) : d319979 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46548, d319979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46548, d319979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46555 q = 0) : d319986 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46555, d319986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33291 q selected
    | true =>
      simp only [d46555, d319986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33292 q selected
  have h6 (q : Pattern) (selected : d46556 q = 0) : d319987 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46556, d319987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46556, d319987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46557 q = 0) : d319988 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46557, d319988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46557, d319988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46571 q = 0) : d320002 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46571, d320002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33295 q selected
    | true =>
      simp only [d46571, d320002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33283 q selected
  have h9 (q : Pattern) (selected : d46635 q = 0) : d319953 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46635, d319953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33306 q selected
    | true =>
      simp only [d46635, d319953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33307 q selected
  have h10 (q : Pattern) (selected : d46636 q = 0) : d320003 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46636, d320003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46636, d320003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46657 q = 0) : d320024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46657, d320024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33312 q selected
    | true =>
      simp only [d46657, d320024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d46658 q = 0) : d320025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46658, d320025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46658, d320025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d46659 q = 0) : d320026 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46659, d320026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46659, d320026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46660 q = 0) : d320027 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46660, d320027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46660, d320027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d46661 q = 0) : d320028 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46661, d320028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46661, d320028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d46665 q = 0) : d320032 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46665, d320032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33314 q selected
    | true =>
      simp only [d46665, d320032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33315 q selected
  have h17 (q : Pattern) (selected : d46666 q = 0) : d320033 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46666, d320033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46666, d320033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d46667 q = 0) : d320034 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46667, d320034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d46667, d320034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d46668 q = 0) : d320035 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46668, d320035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46668, d320035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d46671 q = 0) : d320038 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46671, d320038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33316 q selected
    | true =>
      simp only [d46671, d320038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33317 q selected
  have h21 (q : Pattern) (selected : d46672 q = 0) : d320039 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46672, d320039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46672, d320039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d46673 q = 0) : d320040 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46673, d320040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d46673, d320040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d46675 q = 0) : d320042 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46675, d320042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33318 q selected
    | true =>
      simp only [d46675, d320042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33286 q selected
  have h24 (q : Pattern) (selected : d46678 q = 0) : d319963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46678, d319963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33319 q selected
    | true =>
      simp only [d46678, d319963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33320 q selected
  have h25 (q : Pattern) (selected : d46679 q = 0) : d320043 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46679, d320043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d46679, d320043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d46681 q = 0) : d320045 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46681, d320045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33321 q selected
    | true =>
      simp only [d46681, d320045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d46682 q = 0) : d320046 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46682, d320046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d46682, d320046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d46683 q = 0) : d320047 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46683, d320047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d46683, d320047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d46684 q = 0) : d320048 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46684, d320048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d46684, d320048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d46685 q = 0) : d320049 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46685, d320049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d46685, d320049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d46686 q = 0) : d320050 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46686, d320050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d46686, d320050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro33323 (p : Pattern) (selected : d46693 p = 0) : d320057 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46522 q = 0) : d319953 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46522, d319953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33283 q selected
    | true =>
      simp only [d46522, d319953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33284 q selected
  have h2 (q : Pattern) (selected : d46523 q = 0) : d319954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, d319954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46523, d319954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46524 q = 0) : d319955 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, d319955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46524, d319955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46525 q = 0) : d319956 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, d319956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46525, d319956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46526 q = 0) : d319957 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, d319957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46526, d319957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46688 q = 0) : d320052 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46688, d320052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33284 q selected
    | true =>
      simp only [d46688, d320052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46689 q = 0) : d320053 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46689, d320053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46689, d320053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46690 q = 0) : d320054 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46690, d320054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46690, d320054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46691 q = 0) : d320055 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46691, d320055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46691, d320055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46692 q = 0) : d320056 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46692, d320056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46692, d320056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46693 q = 0) : d320057 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46693, d320057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46693, d320057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro33324 (p : Pattern) (selected : d46699 p = 0) : d320063 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46688 q = 0) : d320052 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46688, d320052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33284 q selected
    | true =>
      simp only [d46688, d320052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46689 q = 0) : d320053 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46689, d320053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46689, d320053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46690 q = 0) : d320054 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46690, d320054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46690, d320054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46691 q = 0) : d320055 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46691, d320055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46691, d320055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46692 q = 0) : d320056 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46692, d320056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46692, d320056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46694 q = 0) : d320058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46694, d320058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33287 q selected
    | true =>
      simp only [d46694, d320058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46695 q = 0) : d320059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46695, d320059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46695, d320059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46696 q = 0) : d320060 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46696, d320060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46696, d320060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46697 q = 0) : d320061 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46697, d320061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46697, d320061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46698 q = 0) : d320062 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46698, d320062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46698, d320062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46699 q = 0) : d320063 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46699, d320063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46699, d320063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro33325 (p : Pattern) (selected : d46706 p = 0) : d320070 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46675 q = 0) : d320042 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46675, d320042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33318 q selected
    | true =>
      simp only [d46675, d320042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33286 q selected
  have h2 (q : Pattern) (selected : d46678 q = 0) : d319963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46678, d319963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33319 q selected
    | true =>
      simp only [d46678, d319963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33320 q selected
  have h3 (q : Pattern) (selected : d46679 q = 0) : d320043 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46679, d320043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46679, d320043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46681 q = 0) : d320045 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46681, d320045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33321 q selected
    | true =>
      simp only [d46681, d320045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46682 q = 0) : d320046 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46682, d320046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46682, d320046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46683 q = 0) : d320047 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46683, d320047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46683, d320047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46704 q = 0) : d320068 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46704, d320068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46704, d320068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46705 q = 0) : d320069 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46705, d320069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46705, d320069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46706 q = 0) : d320070 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46706, d320070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46706, d320070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro33326 (p : Pattern) (selected : d46708 p = 0) : d320072 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46694 q = 0) : d320058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46694, d320058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33287 q selected
    | true =>
      simp only [d46694, d320058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46695 q = 0) : d320059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46695, d320059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46695, d320059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46696 q = 0) : d320060 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46696, d320060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46696, d320060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46697 q = 0) : d320061 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46697, d320061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46697, d320061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46698 q = 0) : d320062 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46698, d320062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46698, d320062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46708 q = 0) : d320072 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46708, d320072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46708, d320072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33327 (p : Pattern) (selected : d46719 p = 0) : d320083 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46714 q = 0) : d320078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46714, d320078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46714, d320078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33274 q selected
  have h2 (q : Pattern) (selected : d46467 q = 0) : d319898 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33274 q selected
    | true =>
      simp only [d46467, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46715 q = 0) : d320079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46715, d320079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46715, d320079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46468 q = 0) : d319899 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46468, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46716 q = 0) : d320080 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46716, d320080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46716, d320080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46717 q = 0) : d320081 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46717, d320081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46717, d320081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46718 q = 0) : d320082 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46718, d320082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46718, d320082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46719 q = 0) : d320083 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46719, d320083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46719, d320083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33328 (p : Pattern) (selected : d46725 p = 0) : d320089 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46714 q = 0) : d320078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46714, d320078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46714, d320078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33274 q selected
  have h2 (q : Pattern) (selected : d46467 q = 0) : d319898 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33274 q selected
    | true =>
      simp only [d46467, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46715 q = 0) : d320079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46715, d320079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46715, d320079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46468 q = 0) : d319899 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46468, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46716 q = 0) : d320080 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46716, d320080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46716, d320080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46717 q = 0) : d320081 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46717, d320081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46717, d320081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46718 q = 0) : d320082 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46718, d320082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46718, d320082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46720 q = 0) : d320084 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46720, d320084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46720, d320084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33276 q selected
  have h9 (q : Pattern) (selected : d46483 q = 0) : d319914 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33276 q selected
    | true =>
      simp only [d46483, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46721 q = 0) : d320085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46721, d320085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46721, d320085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46484 q = 0) : d319915 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46484, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d46722 q = 0) : d320086 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46722, d320086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46722, d320086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46723 q = 0) : d320087 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46723, d320087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46723, d320087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d46724 q = 0) : d320088 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46724, d320088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46724, d320088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d46725 q = 0) : d320089 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46725, d320089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46725, d320089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro33329 (p : Pattern) (selected : d46730 p = 0) : d320094 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46714 q = 0) : d320078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46714, d320078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46714, d320078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33274 q selected
  have h2 (q : Pattern) (selected : d46467 q = 0) : d319898 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33274 q selected
    | true =>
      simp only [d46467, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46715 q = 0) : d320079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46715, d320079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46715, d320079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46468 q = 0) : d319899 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46468, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46716 q = 0) : d320080 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46716, d320080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46716, d320080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46717 q = 0) : d320081 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46717, d320081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46717, d320081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46720 q = 0) : d320084 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46720, d320084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46720, d320084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33276 q selected
  have h8 (q : Pattern) (selected : d46483 q = 0) : d319914 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33276 q selected
    | true =>
      simp only [d46483, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46721 q = 0) : d320085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46721, d320085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46721, d320085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46484 q = 0) : d319915 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46484, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46722 q = 0) : d320086 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46722, d320086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46722, d320086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d46723 q = 0) : d320087 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46723, d320087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46723, d320087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d46724 q = 0) : d320088 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46724, d320088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46724, d320088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46729 q = 0) : d320093 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46729, d320093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46729, d320093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46730 q = 0) : d320094 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46730, d320094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46730, d320094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro33330 (p : Pattern) (selected : d46740 p = 0) : d320104 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46720 q = 0) : d320084 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46720, d320084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46720, d320084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33276 q selected
  have h2 (q : Pattern) (selected : d46483 q = 0) : d319914 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33276 q selected
    | true =>
      simp only [d46483, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46721 q = 0) : d320085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46721, d320085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46721, d320085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46484 q = 0) : d319915 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46484, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46722 q = 0) : d320086 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46722, d320086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46722, d320086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46723 q = 0) : d320087 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46723, d320087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46723, d320087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46729 q = 0) : d320093 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46729, d320093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46729, d320093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46735 q = 0) : d320099 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46735, d320099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46735, d320099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33279 q selected
  have h9 (q : Pattern) (selected : d46495 q = 0) : d319926 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46495, d319926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33279 q selected
    | true =>
      simp only [d46495, d319926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46736 q = 0) : d320100 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46736, d320100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46736, d320100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46496 q = 0) : d319927 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46496, d319927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46496, d319927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d46737 q = 0) : d320101 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46737, d320101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46737, d320101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46738 q = 0) : d320102 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46738, d320102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46738, d320102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d46739 q = 0) : d320103 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46739, d320103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46739, d320103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46740 q = 0) : d320104 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46740, d320104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46740, d320104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro33331 (p : Pattern) (selected : d46746 p = 0) : d320110 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46726 q = 0) : d320090 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46726, d320090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33327 q selected
    | true =>
      simp only [d46726, d320090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33328 q selected
  have h2 (q : Pattern) (selected : d46727 q = 0) : d320091 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46727, d320091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46727, d320091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46728 q = 0) : d320092 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46728, d320092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46728, d320092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46731 q = 0) : d320095 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46731, d320095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33328 q selected
    | true =>
      simp only [d46731, d320095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33329 q selected
  have h5 (q : Pattern) (selected : d46732 q = 0) : d320096 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46732, d320096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46732, d320096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46733 q = 0) : d320097 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46733, d320097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46733, d320097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46734 q = 0) : d320098 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46734, d320098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46734, d320098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46741 q = 0) : d320105 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46741, d320105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33329 q selected
    | true =>
      simp only [d46741, d320105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33330 q selected
  have h9 (q : Pattern) (selected : d46742 q = 0) : d320106 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46742, d320106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46742, d320106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46743 q = 0) : d320107 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46743, d320107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46743, d320107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46744 q = 0) : d320108 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46744, d320108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46744, d320108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d46745 q = 0) : d320109 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46745, d320109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46745, d320109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46746 q = 0) : d320110 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46746, d320110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46746, d320110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro33332 (p : Pattern) (selected : d46751 p = 0) : d320115 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46731 q = 0) : d320095 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46731, d320095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33328 q selected
    | true =>
      simp only [d46731, d320095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33329 q selected
  have h2 (q : Pattern) (selected : d46732 q = 0) : d320096 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46732, d320096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46732, d320096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46733 q = 0) : d320097 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46733, d320097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46733, d320097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46741 q = 0) : d320105 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46741, d320105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33329 q selected
    | true =>
      simp only [d46741, d320105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33330 q selected
  have h5 (q : Pattern) (selected : d46742 q = 0) : d320106 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46742, d320106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46742, d320106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46743 q = 0) : d320107 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46743, d320107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46743, d320107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46744 q = 0) : d320108 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46744, d320108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46744, d320108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46749 q = 0) : d320113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46749, d320113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46749, d320113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46750 q = 0) : d320114 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46750, d320114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46750, d320114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46751 q = 0) : d320115 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46751, d320115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46751, d320115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro33333 (p : Pattern) (selected : d46757 p = 0) : d320121 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46747 q = 0) : d320111 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46747, d320111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33331 q selected
    | true =>
      simp only [d46747, d320111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46748 q = 0) : d320112 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46748, d320112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46748, d320112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46752 q = 0) : d320116 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46752, d320116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33332 q selected
    | true =>
      simp only [d46752, d320116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46753 q = 0) : d320117 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46753, d320117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46753, d320117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46754 q = 0) : d320118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46754, d320118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46754, d320118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46755 q = 0) : d320119 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46755, d320119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46755, d320119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46756 q = 0) : d320120 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46756, d320120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46756, d320120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46757 q = 0) : d320121 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46757, d320121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46757, d320121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33334 (p : Pattern) (selected : d46759 p = 0) : d320123 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46741 q = 0) : d320105 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46741, d320105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33329 q selected
    | true =>
      simp only [d46741, d320105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33330 q selected
  have h2 (q : Pattern) (selected : d46742 q = 0) : d320106 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46742, d320106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46742, d320106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46743 q = 0) : d320107 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46743, d320107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46743, d320107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46749 q = 0) : d320113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46749, d320113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46749, d320113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46758 q = 0) : d320122 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46758, d320122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46758, d320122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46759 q = 0) : d320123 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46759, d320123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46759, d320123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33335 (p : Pattern) (selected : d46765 p = 0) : d320129 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46752 q = 0) : d320116 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46752, d320116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33332 q selected
    | true =>
      simp only [d46752, d320116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46753 q = 0) : d320117 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46753, d320117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46753, d320117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46760 q = 0) : d320124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46760, d320124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33334 q selected
    | true =>
      simp only [d46760, d320124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46761 q = 0) : d320125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46761, d320125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46761, d320125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46762 q = 0) : d320126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46762, d320126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46762, d320126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46763 q = 0) : d320127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46763, d320127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46763, d320127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46764 q = 0) : d320128 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46764, d320128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46764, d320128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46765 q = 0) : d320129 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46765, d320129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46765, d320129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33336 (p : Pattern) (selected : d46777 p = 0) : d320089 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46767 q = 0) : d320078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46767, d320078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46767, d320078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33297 q selected
  have h2 (q : Pattern) (selected : d46580 q = 0) : d319898 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46580, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33297 q selected
    | true =>
      simp only [d46580, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46768 q = 0) : d320079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46768, d320079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46768, d320079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46581 q = 0) : d319899 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46581, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46581, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46769 q = 0) : d320080 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46769, d320080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46769, d320080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46770 q = 0) : d320081 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46770, d320081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46770, d320081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46771 q = 0) : d320082 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46771, d320082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46771, d320082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46772 q = 0) : d320084 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46772, d320084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46772, d320084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33299 q selected
  have h9 (q : Pattern) (selected : d46596 q = 0) : d319914 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46596, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33299 q selected
    | true =>
      simp only [d46596, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46773 q = 0) : d320085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46773, d320085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46773, d320085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46597 q = 0) : d319915 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46597, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46597, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d46774 q = 0) : d320086 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46774, d320086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46774, d320086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46775 q = 0) : d320087 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46775, d320087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46775, d320087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d46776 q = 0) : d320088 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46776, d320088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46776, d320088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d46777 q = 0) : d320089 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46777, d320089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46777, d320089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro33337 (p : Pattern) (selected : d46779 p = 0) : d320094 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46767 q = 0) : d320078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46767, d320078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46767, d320078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33297 q selected
  have h2 (q : Pattern) (selected : d46580 q = 0) : d319898 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46580, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33297 q selected
    | true =>
      simp only [d46580, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46768 q = 0) : d320079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46768, d320079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46768, d320079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46581 q = 0) : d319899 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46581, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46581, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46769 q = 0) : d320080 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46769, d320080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46769, d320080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46770 q = 0) : d320081 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46770, d320081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46770, d320081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46772 q = 0) : d320084 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46772, d320084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46772, d320084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33299 q selected
  have h8 (q : Pattern) (selected : d46596 q = 0) : d319914 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46596, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33299 q selected
    | true =>
      simp only [d46596, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46773 q = 0) : d320085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46773, d320085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46773, d320085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46597 q = 0) : d319915 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46597, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46597, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46774 q = 0) : d320086 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46774, d320086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46774, d320086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d46775 q = 0) : d320087 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46775, d320087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46775, d320087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d46776 q = 0) : d320088 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46776, d320088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46776, d320088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46778 q = 0) : d320093 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46778, d320093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46778, d320093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46779 q = 0) : d320094 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46779, d320094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46779, d320094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro33338 (p : Pattern) (selected : d46788 p = 0) : d320104 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46772 q = 0) : d320084 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46772, d320084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46772, d320084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33299 q selected
  have h2 (q : Pattern) (selected : d46596 q = 0) : d319914 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46596, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33299 q selected
    | true =>
      simp only [d46596, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46773 q = 0) : d320085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46773, d320085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46773, d320085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46597 q = 0) : d319915 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46597, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46597, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46774 q = 0) : d320086 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46774, d320086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46774, d320086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46775 q = 0) : d320087 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46775, d320087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46775, d320087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46778 q = 0) : d320093 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46778, d320093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46778, d320093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46783 q = 0) : d320099 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46783, d320099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46783, d320099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33302 q selected
  have h9 (q : Pattern) (selected : d46608 q = 0) : d319926 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46608, d319926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33302 q selected
    | true =>
      simp only [d46608, d319926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46784 q = 0) : d320100 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46784, d320100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46784, d320100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46609 q = 0) : d319927 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46609, d319927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46609, d319927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d46785 q = 0) : d320101 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46785, d320101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46785, d320101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46786 q = 0) : d320102 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46786, d320102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46786, d320102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d46787 q = 0) : d320103 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46787, d320103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46787, d320103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46788 q = 0) : d320104 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46788, d320104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46788, d320104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro33339 (p : Pattern) (selected : d46795 p = 0) : d320115 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46780 q = 0) : d320095 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46780, d320095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33336 q selected
    | true =>
      simp only [d46780, d320095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33337 q selected
  have h2 (q : Pattern) (selected : d46781 q = 0) : d320096 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46781, d320096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46781, d320096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46782 q = 0) : d320097 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46782, d320097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46782, d320097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46789 q = 0) : d320105 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46789, d320105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33337 q selected
    | true =>
      simp only [d46789, d320105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33338 q selected
  have h5 (q : Pattern) (selected : d46790 q = 0) : d320106 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46790, d320106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46790, d320106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46791 q = 0) : d320107 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46791, d320107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46791, d320107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46792 q = 0) : d320108 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46792, d320108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46792, d320108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46793 q = 0) : d320113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46793, d320113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46793, d320113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46794 q = 0) : d320114 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46794, d320114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46794, d320114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46795 q = 0) : d320115 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46795, d320115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46795, d320115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro33340 (p : Pattern) (selected : d46799 p = 0) : d320123 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46789 q = 0) : d320105 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46789, d320105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33337 q selected
    | true =>
      simp only [d46789, d320105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33338 q selected
  have h2 (q : Pattern) (selected : d46790 q = 0) : d320106 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46790, d320106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46790, d320106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46791 q = 0) : d320107 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46791, d320107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46791, d320107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46793 q = 0) : d320113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46793, d320113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46793, d320113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46798 q = 0) : d320122 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46798, d320122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46798, d320122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46799 q = 0) : d320123 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46799, d320123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46799, d320123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33341 (p : Pattern) (selected : d46805 p = 0) : d320129 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46796 q = 0) : d320116 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46796, d320116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33339 q selected
    | true =>
      simp only [d46796, d320116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46797 q = 0) : d320117 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46797, d320117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46797, d320117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46800 q = 0) : d320124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46800, d320124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33340 q selected
    | true =>
      simp only [d46800, d320124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46801 q = 0) : d320125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46801, d320125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46801, d320125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46802 q = 0) : d320126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46802, d320126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46802, d320126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46803 q = 0) : d320127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46803, d320127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46803, d320127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46804 q = 0) : d320128 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46804, d320128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46804, d320128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46805 q = 0) : d320129 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46805, d320129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46805, d320129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33342 (p : Pattern) (selected : d46809 p = 0) : d320134 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46800 q = 0) : d320124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46800, d320124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33340 q selected
    | true =>
      simp only [d46800, d320124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46801 q = 0) : d320125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46801, d320125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46801, d320125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46806 q = 0) : d320131 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46806, d320131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46806, d320131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46807 q = 0) : d320132 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46807, d320132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46807, d320132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46808 q = 0) : d320133 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46808, d320133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46808, d320133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46809 q = 0) : d320134 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46809, d320134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46809, d320134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33343 (p : Pattern) (selected : d46817 p = 0) : d320142 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46714 q = 0) : d320078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46714, d320078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46714, d320078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33274 q selected
  have h2 (q : Pattern) (selected : d46467 q = 0) : d319898 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33274 q selected
    | true =>
      simp only [d46467, d319898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46715 q = 0) : d320079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46715, d320079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46715, d320079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46468 q = 0) : d319899 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46468, d319899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46716 q = 0) : d320080 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46716, d320080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46716, d320080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46717 q = 0) : d320081 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46717, d320081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46717, d320081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46720 q = 0) : d320084 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46720, d320084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46720, d320084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33276 q selected
  have h8 (q : Pattern) (selected : d46483 q = 0) : d319914 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33276 q selected
    | true =>
      simp only [d46483, d319914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46721 q = 0) : d320085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46721, d320085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46721, d320085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46484 q = 0) : d319915 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46484, d319915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46722 q = 0) : d320086 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46722, d320086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46722, d320086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d46723 q = 0) : d320087 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46723, d320087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46723, d320087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d46724 q = 0) : d320088 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46724, d320088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46724, d320088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46812 q = 0) : d320137 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46812, d320137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46812, d320137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33308 q selected
  have h15 (q : Pattern) (selected : d46638 q = 0) : d320005 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46638, d320005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33308 q selected
    | true =>
      simp only [d46638, d320005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d46813 q = 0) : d320138 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46813, d320138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d46813, d320138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d46639 q = 0) : d320006 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46639, d320006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d46639, d320006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d46814 q = 0) : d320139 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46814, d320139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d46814, d320139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d46815 q = 0) : d320140 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46815, d320140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d46815, d320140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d46816 q = 0) : d320141 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46816, d320141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d46816, d320141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d46817 q = 0) : d320142 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46817, d320142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46817, d320142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro33344 (p : Pattern) (selected : d46818 p = 0) : d320143 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46812 q = 0) : d320137 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46812, d320137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46812, d320137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33308 q selected
  have h2 (q : Pattern) (selected : d46638 q = 0) : d320005 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46638, d320005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33308 q selected
    | true =>
      simp only [d46638, d320005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46813 q = 0) : d320138 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46813, d320138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46813, d320138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46639 q = 0) : d320006 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46639, d320006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46639, d320006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46814 q = 0) : d320139 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46814, d320139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46814, d320139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46815 q = 0) : d320140 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46815, d320140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46815, d320140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46816 q = 0) : d320141 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46816, d320141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46816, d320141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46818 q = 0) : d320143 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46818, d320143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46818, d320143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33345 (p : Pattern) (selected : d46824 p = 0) : d320149 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46731 q = 0) : d320095 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46731, d320095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33328 q selected
    | true =>
      simp only [d46731, d320095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33329 q selected
  have h2 (q : Pattern) (selected : d46732 q = 0) : d320096 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46732, d320096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46732, d320096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46733 q = 0) : d320097 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46733, d320097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46733, d320097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46741 q = 0) : d320105 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46741, d320105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33329 q selected
    | true =>
      simp only [d46741, d320105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33330 q selected
  have h5 (q : Pattern) (selected : d46742 q = 0) : d320106 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46742, d320106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46742, d320106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46743 q = 0) : d320107 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46743, d320107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46743, d320107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46744 q = 0) : d320108 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46744, d320108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46744, d320108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46819 q = 0) : d320144 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46819, d320144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33343 q selected
    | true =>
      simp only [d46819, d320144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33344 q selected
  have h9 (q : Pattern) (selected : d46820 q = 0) : d320145 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46820, d320145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46820, d320145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46821 q = 0) : d320146 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46821, d320146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46821, d320146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46822 q = 0) : d320147 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46822, d320147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46822, d320147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d46823 q = 0) : d320148 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46823, d320148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46823, d320148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46824 q = 0) : d320149 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46824, d320149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46824, d320149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro33346 (p : Pattern) (selected : d46830 p = 0) : d320155 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46825 q = 0) : d320150 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46825, d320150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33345 q selected
    | true =>
      simp only [d46825, d320150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46826 q = 0) : d320151 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46826, d320151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46826, d320151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46827 q = 0) : d320152 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46827, d320152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46827, d320152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46828 q = 0) : d320153 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46828, d320153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46828, d320153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46829 q = 0) : d320154 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46829, d320154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46829, d320154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46830 q = 0) : d320155 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46830, d320155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46830, d320155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33347 (p : Pattern) (selected : d46836 p = 0) : d320161 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46766 q = 0) : d320130 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46766, d320130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33333 q selected
    | true =>
      simp only [d46766, d320130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33335 q selected
  have h2 (q : Pattern) (selected : d46810 q = 0) : d320135 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46810, d320135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33341 q selected
    | true =>
      simp only [d46810, d320135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33342 q selected
  have h3 (q : Pattern) (selected : d46811 q = 0) : d320136 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46811, d320136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46811, d320136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46831 q = 0) : d320156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46831, d320156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33346 q selected
    | true =>
      simp only [d46831, d320156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46832 q = 0) : d320157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46832, d320157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46832, d320157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46833 q = 0) : d320158 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46833, d320158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46833, d320158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46834 q = 0) : d320159 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46834, d320159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46834, d320159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46835 q = 0) : d320160 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46835, d320160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46835, d320160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46836 q = 0) : d320161 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46836, d320161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46836, d320161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro33348 (p : Pattern) (selected : d46841 p = 0) : d320134 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46760 q = 0) : d320124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46760, d320124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33334 q selected
    | true =>
      simp only [d46760, d320124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46761 q = 0) : d320125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46761, d320125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46761, d320125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46838 q = 0) : d320131 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46838, d320131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46838, d320131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46839 q = 0) : d320132 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46839, d320132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46839, d320132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46840 q = 0) : d320133 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46840, d320133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46840, d320133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46841 q = 0) : d320134 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46841, d320134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46841, d320134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33349 (p : Pattern) (selected : d46847 p = 0) : d320168 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46842 q = 0) : d320163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46842, d320163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33348 q selected
    | true =>
      simp only [d46842, d320163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46843 q = 0) : d320164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46843, d320164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46843, d320164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46844 q = 0) : d320165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46844, d320165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46844, d320165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46845 q = 0) : d320166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46845, d320166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46845, d320166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46846 q = 0) : d320167 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46846, d320167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46846, d320167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46847 q = 0) : d320168 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46847, d320168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46847, d320168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33350 (p : Pattern) (selected : d46853 p = 0) : d320174 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46528 q = 0) : d319959 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46528, d319959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46528, d319959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33285 q selected
  have h2 (q : Pattern) (selected : d46529 q = 0) : d319960 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46529, d319960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46529, d319960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46538 q = 0) : d319969 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46538, d319969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33285 q selected
    | true =>
      simp only [d46538, d319969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33288 q selected
  have h4 (q : Pattern) (selected : d46539 q = 0) : d319970 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46539, d319970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46539, d319970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46540 q = 0) : d319971 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46540, d319971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46540, d319971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46687 q = 0) : d320051 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46687, d320051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33313 q selected
    | true =>
      simp only [d46687, d320051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33322 q selected
  have h7 (q : Pattern) (selected : d46700 q = 0) : d320064 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46700, d320064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33323 q selected
    | true =>
      simp only [d46700, d320064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33324 q selected
  have h8 (q : Pattern) (selected : d46701 q = 0) : d320065 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46701, d320065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46701, d320065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46702 q = 0) : d320066 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46702, d320066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46702, d320066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46703 q = 0) : d320067 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d46703, d320067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46703, d320067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46707 q = 0) : d320071 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46707, d320071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46707, d320071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33325 q selected
  have h12 (q : Pattern) (selected : d46709 q = 0) : d320073 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46709, d320073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46709, d320073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33326 q selected
  have h13 (q : Pattern) (selected : d46710 q = 0) : d320074 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46710, d320074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d46710, d320074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d46711 q = 0) : d320075 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46711, d320075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d46711, d320075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d46712 q = 0) : d320076 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d46712, d320076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d46712, d320076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d46713 q = 0) : d320077 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d46713, d320077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d46713, d320077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d46837 q = 0) : d320162 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46837, d320162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46837, d320162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33347 q selected
  have h18 (q : Pattern) (selected : d46848 q = 0) : d320169 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46848, d320169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46848, d320169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33349 q selected
  have h19 (q : Pattern) (selected : d46849 q = 0) : d320170 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46849, d320170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d46849, d320170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d46850 q = 0) : d320171 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46850, d320171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d46850, d320171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d46851 q = 0) : d320172 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d46851, d320172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d46851, d320172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d46852 q = 0) : d320173 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d46852, d320173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d46852, d320173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d46853 q = 0) : d320174 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d46853, d320174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d46853, d320174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro33351 (p : Pattern) (selected : d46859 p = 0) : d320180 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46854 q = 0) : d320175 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d46854, d320175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46854, d320175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33350 q selected
  have h2 (q : Pattern) (selected : d46855 q = 0) : d320176 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d46855, d320176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46855, d320176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46856 q = 0) : d320177 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d46856, d320177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46856, d320177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46857 q = 0) : d320178 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d46857, d320178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46857, d320178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46858 q = 0) : d320179 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d46858, d320179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46858, d320179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46859 q = 0) : d320180 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d46859, d320180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46859, d320180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33352 (p : Pattern) (selected : d46867 p = 0) : d320185 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d13 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44880 q = 0) : d263912 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d44880, d263912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44880, d263912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46864 q = 0) : d263913 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d46864, d263913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46864, d263913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46865 q = 0) : d263914 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d46865, d263914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46865, d263914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46866 q = 0) : d263915 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46866, d263915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46866, d263915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46867 q = 0) : d320185 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46867, d320185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46867, d320185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro33353 (p : Pattern) (selected : d46876 p = 0) : d320194 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46868 q = 0) : d320186 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46868, d320186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46868, d320186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33352 q selected
  have h2 (q : Pattern) (selected : d46869 q = 0) : d320187 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46869, d320187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46869, d320187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46870 q = 0) : d320188 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46870, d320188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46870, d320188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46871 q = 0) : d320189 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d320189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33352 q selected
    | true =>
      simp only [d46871, d320189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46872 q = 0) : d320190 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46872, d320190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46872, d320190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46873 q = 0) : d320191 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46873, d320191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46873, d320191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46874 q = 0) : d320192 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46874, d320192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46874, d320192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46875 q = 0) : d320193 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46875, d320193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46875, d320193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46876 q = 0) : d320194 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46876, d320194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46876, d320194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro33354 (p : Pattern) (selected : d46882 p = 0) : d320200 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46877 q = 0) : d320195 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33353 q selected
    | true =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46878 q = 0) : d320196 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46879 q = 0) : d320197 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, d320197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46879, d320197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46880 q = 0) : d320198 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, d320198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46880, d320198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46881 q = 0) : d320199 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46881, d320199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46881, d320199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46882 q = 0) : d320200 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46882, d320200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46882, d320200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33355 (p : Pattern) (selected : d46884 p = 0) : d320202 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46877 q = 0) : d320195 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33353 q selected
    | true =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46878 q = 0) : d320196 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46879 q = 0) : d320197 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, d320197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46879, d320197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46880 q = 0) : d320198 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, d320198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46880, d320198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46881 q = 0) : d320199 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46881, d320199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46881, d320199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46883 q = 0) : d320201 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46883, d320201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46883, d320201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46884 q = 0) : d320202 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46884, d320202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46884, d320202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro33356 (p : Pattern) (selected : d46888 p = 0) : d320206 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46868 q = 0) : d320186 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46868, d320186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46868, d320186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33352 q selected
  have h2 (q : Pattern) (selected : d46869 q = 0) : d320187 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46869, d320187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46869, d320187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46870 q = 0) : d320188 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46870, d320188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46870, d320188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46871 q = 0) : d320189 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d320189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33352 q selected
    | true =>
      simp only [d46871, d320189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46872 q = 0) : d320190 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46872, d320190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46872, d320190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46873 q = 0) : d320191 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46873, d320191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46873, d320191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46874 q = 0) : d320192 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46874, d320192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46874, d320192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46875 q = 0) : d320193 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46875, d320193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46875, d320193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46888 q = 0) : d320206 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46888, d320206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46888, d320206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro33357 (p : Pattern) (selected : d46894 p = 0) : d320212 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46877 q = 0) : d320195 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33353 q selected
    | true =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46878 q = 0) : d320196 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46879 q = 0) : d320197 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, d320197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46879, d320197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46880 q = 0) : d320198 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, d320198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46880, d320198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46883 q = 0) : d320201 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46883, d320201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46883, d320201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46889 q = 0) : d320207 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46889, d320207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33356 q selected
    | true =>
      simp only [d46889, d320207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46890 q = 0) : d320208 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46890, d320208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46890, d320208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46891 q = 0) : d320209 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46891, d320209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46891, d320209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46892 q = 0) : d320210 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46892, d320210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46892, d320210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46893 q = 0) : d320211 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46893, d320211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46893, d320211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46894 q = 0) : d320212 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46894, d320212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46894, d320212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro33358 (p : Pattern) (selected : d46901 p = 0) : d320219 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46885 q = 0) : d320203 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46885, d320203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33354 q selected
    | true =>
      simp only [d46885, d320203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33355 q selected
  have h2 (q : Pattern) (selected : d46886 q = 0) : d320204 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46886, d320204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46886, d320204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46887 q = 0) : d320205 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46887, d320205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46887, d320205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46895 q = 0) : d320213 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, d320213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33355 q selected
    | true =>
      simp only [d46895, d320213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33357 q selected
  have h5 (q : Pattern) (selected : d46896 q = 0) : d320214 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, d320214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46896, d320214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46897 q = 0) : d320215 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, d320215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46897, d320215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46898 q = 0) : d320216 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46898, d320216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46898, d320216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46899 q = 0) : d320217 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46899, d320217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46899, d320217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46900 q = 0) : d320218 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46900, d320218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46900, d320218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46901 q = 0) : d320219 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46901, d320219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46901, d320219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro33359 (p : Pattern) (selected : d46905 p = 0) : d320223 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46895 q = 0) : d320213 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, d320213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33355 q selected
    | true =>
      simp only [d46895, d320213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33357 q selected
  have h2 (q : Pattern) (selected : d46896 q = 0) : d320214 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, d320214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46896, d320214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46897 q = 0) : d320215 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, d320215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46897, d320215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46899 q = 0) : d320217 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46899, d320217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46899, d320217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46904 q = 0) : d320222 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46904, d320222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46904, d320222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46905 q = 0) : d320223 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46905, d320223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46905, d320223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33360 (p : Pattern) (selected : d46911 p = 0) : d320229 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46902 q = 0) : d320220 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33358 q selected
    | true =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46903 q = 0) : d320221 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46906 q = 0) : d320224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33359 q selected
    | true =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46907 q = 0) : d320225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46908 q = 0) : d320226 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, d320226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46908, d320226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46909 q = 0) : d320227 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, d320227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46909, d320227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46910 q = 0) : d320228 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46910, d320228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46910, d320228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46911 q = 0) : d320229 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46911, d320229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46911, d320229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33361 (p : Pattern) (selected : d46915 p = 0) : d320233 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46906 q = 0) : d320224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33359 q selected
    | true =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46907 q = 0) : d320225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46912 q = 0) : d320230 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, d320230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46912, d320230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46913 q = 0) : d320231 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46913, d320231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46913, d320231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46914 q = 0) : d320232 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46914, d320232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46914, d320232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46915 q = 0) : d320233 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46915, d320233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46915, d320233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33362 (p : Pattern) (selected : d46921 p = 0) : d320239 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46916 q = 0) : d320234 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46916, d320234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33360 q selected
    | true =>
      simp only [d46916, d320234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33361 q selected
  have h2 (q : Pattern) (selected : d46917 q = 0) : d320235 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, d320235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46917, d320235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46918 q = 0) : d320236 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, d320236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46918, d320236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46919 q = 0) : d320237 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, d320237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46919, d320237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46920 q = 0) : d320238 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, d320238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46920, d320238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46921 q = 0) : d320239 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46921, d320239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46921, d320239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33363 (p : Pattern) (selected : d46924 p = 0) : d320242 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46902 q = 0) : d320220 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33358 q selected
    | true =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46903 q = 0) : d320221 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46906 q = 0) : d320224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33359 q selected
    | true =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46907 q = 0) : d320225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46908 q = 0) : d320226 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, d320226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46908, d320226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46909 q = 0) : d320227 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, d320227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46909, d320227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46910 q = 0) : d320228 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46910, d320228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46910, d320228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46924 q = 0) : d320242 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46924, d320242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46924, d320242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33364 (p : Pattern) (selected : d46925 p = 0) : d320243 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46906 q = 0) : d320224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33359 q selected
    | true =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46907 q = 0) : d320225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46912 q = 0) : d320230 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, d320230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46912, d320230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46913 q = 0) : d320231 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46913, d320231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46913, d320231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46914 q = 0) : d320232 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46914, d320232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46914, d320232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46925 q = 0) : d320243 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46925, d320243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46925, d320243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33365 (p : Pattern) (selected : d46931 p = 0) : d320249 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46916 q = 0) : d320234 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46916, d320234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33360 q selected
    | true =>
      simp only [d46916, d320234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33361 q selected
  have h2 (q : Pattern) (selected : d46917 q = 0) : d320235 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, d320235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46917, d320235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46918 q = 0) : d320236 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, d320236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46918, d320236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46919 q = 0) : d320237 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, d320237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46919, d320237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46920 q = 0) : d320238 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, d320238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46920, d320238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46926 q = 0) : d320244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46926, d320244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33363 q selected
    | true =>
      simp only [d46926, d320244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33364 q selected
  have h7 (q : Pattern) (selected : d46927 q = 0) : d320245 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46927, d320245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46927, d320245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46928 q = 0) : d320246 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46928, d320246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46928, d320246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46929 q = 0) : d320247 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46929, d320247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46929, d320247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46930 q = 0) : d320248 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46930, d320248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46930, d320248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46931 q = 0) : d320249 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46931, d320249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46931, d320249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro33366 (p : Pattern) (selected : d46936 p = 0) : d320254 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46902 q = 0) : d320220 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33358 q selected
    | true =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46903 q = 0) : d320221 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46906 q = 0) : d320224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33359 q selected
    | true =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46907 q = 0) : d320225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46908 q = 0) : d320226 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, d320226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46908, d320226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46909 q = 0) : d320227 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, d320227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46909, d320227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46935 q = 0) : d320253 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46935, d320253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46935, d320253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46936 q = 0) : d320254 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46936, d320254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46936, d320254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33367 (p : Pattern) (selected : d46938 p = 0) : d320256 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46906 q = 0) : d320224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33359 q selected
    | true =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46907 q = 0) : d320225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46912 q = 0) : d320230 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, d320230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46912, d320230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46913 q = 0) : d320231 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46913, d320231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46913, d320231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46937 q = 0) : d320255 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46937, d320255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46937, d320255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46938 q = 0) : d320256 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46938, d320256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46938, d320256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33368 (p : Pattern) (selected : d46945 p = 0) : d320263 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46902 q = 0) : d320220 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33358 q selected
    | true =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46903 q = 0) : d320221 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46906 q = 0) : d320224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33359 q selected
    | true =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46907 q = 0) : d320225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46908 q = 0) : d320226 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, d320226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46908, d320226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46943 q = 0) : d320261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46943, d320261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46943, d320261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46944 q = 0) : d320262 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46944, d320262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46944, d320262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46945 q = 0) : d320263 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46945, d320263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46945, d320263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33369 (p : Pattern) (selected : d46948 p = 0) : d320266 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46906 q = 0) : d320224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33359 q selected
    | true =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46907 q = 0) : d320225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46912 q = 0) : d320230 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, d320230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46912, d320230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46946 q = 0) : d320264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46946, d320264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46946, d320264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46947 q = 0) : d320265 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46947, d320265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46947, d320265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46948 q = 0) : d320266 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46948, d320266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46948, d320266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33370 (p : Pattern) (selected : d46957 p = 0) : d320275 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46952 q = 0) : d320270 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46952, d320270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46952, d320270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33354 q selected
  have h2 (q : Pattern) (selected : d46953 q = 0) : d320271 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46953, d320271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46953, d320271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46954 q = 0) : d320272 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46954, d320272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46954, d320272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46885 q = 0) : d320203 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46885, d320203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33354 q selected
    | true =>
      simp only [d46885, d320203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33355 q selected
  have h5 (q : Pattern) (selected : d46886 q = 0) : d320204 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46886, d320204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46886, d320204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46887 q = 0) : d320205 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46887, d320205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46887, d320205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46955 q = 0) : d320273 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46955, d320273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46955, d320273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46895 q = 0) : d320213 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, d320213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33355 q selected
    | true =>
      simp only [d46895, d320213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33357 q selected
  have h9 (q : Pattern) (selected : d46896 q = 0) : d320214 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, d320214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46896, d320214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46897 q = 0) : d320215 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, d320215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46897, d320215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46898 q = 0) : d320216 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46898, d320216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46898, d320216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d46956 q = 0) : d320274 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46956, d320274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46956, d320274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d46957 q = 0) : d320275 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46957, d320275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d46957, d320275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro33371 (p : Pattern) (selected : d46963 p = 0) : d320281 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46958 q = 0) : d320276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46958, d320276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33370 q selected
    | true =>
      simp only [d46958, d320276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46959 q = 0) : d320277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46959, d320277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46959, d320277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46902 q = 0) : d320220 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33358 q selected
    | true =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46903 q = 0) : d320221 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46960 q = 0) : d320278 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46960, d320278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46960, d320278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46961 q = 0) : d320279 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46961, d320279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46961, d320279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46962 q = 0) : d320280 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46962, d320280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46962, d320280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46963 q = 0) : d320281 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46963, d320281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46963, d320281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33372 (p : Pattern) (selected : d46965 p = 0) : d320185 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d158 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d35873 q = 0) : d263912 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d35873, d263912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d35873, d263912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d35874 q = 0) : d263913 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d35874, d263913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d35874, d263913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d35875 q = 0) : d263914 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d35875, d263914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d35875, d263914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d35876 q = 0) : d263915 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d35876, d263915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d35876, d263915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46965 q = 0) : d320185 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46965, d320185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46965, d320185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro33373 (p : Pattern) (selected : d46974 p = 0) : d320194 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46966 q = 0) : d320186 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46966, d320186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46966, d320186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33372 q selected
  have h2 (q : Pattern) (selected : d46967 q = 0) : d320187 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46967, d320187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46967, d320187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46968 q = 0) : d320188 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46968, d320188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46968, d320188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46969 q = 0) : d320189 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46969, d320189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33372 q selected
    | true =>
      simp only [d46969, d320189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46970 q = 0) : d320190 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46970, d320190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46970, d320190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46971 q = 0) : d320191 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46971, d320191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46971, d320191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46972 q = 0) : d320192 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46972, d320192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46972, d320192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46973 q = 0) : d320193 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46973, d320193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46973, d320193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46974 q = 0) : d320194 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46974, d320194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46974, d320194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro33374 (p : Pattern) (selected : d46980 p = 0) : d320200 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46975 q = 0) : d320195 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46975, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33373 q selected
    | true =>
      simp only [d46975, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46976 q = 0) : d320196 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46976, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46976, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46977 q = 0) : d320197 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46977, d320197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46977, d320197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46978 q = 0) : d320198 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46978, d320198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46978, d320198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46979 q = 0) : d320199 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46979, d320199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46979, d320199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46980 q = 0) : d320200 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46980, d320200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46980, d320200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33375 (p : Pattern) (selected : d46982 p = 0) : d320202 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46975 q = 0) : d320195 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46975, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33373 q selected
    | true =>
      simp only [d46975, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46976 q = 0) : d320196 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46976, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46976, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46977 q = 0) : d320197 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46977, d320197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46977, d320197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46978 q = 0) : d320198 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46978, d320198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46978, d320198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46979 q = 0) : d320199 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46979, d320199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46979, d320199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46981 q = 0) : d320201 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46981, d320201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46981, d320201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46982 q = 0) : d320202 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46982, d320202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46982, d320202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro33376 (p : Pattern) (selected : d46986 p = 0) : d320206 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46966 q = 0) : d320186 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46966, d320186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46966, d320186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33372 q selected
  have h2 (q : Pattern) (selected : d46967 q = 0) : d320187 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46967, d320187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46967, d320187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46968 q = 0) : d320188 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46968, d320188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46968, d320188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46969 q = 0) : d320189 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46969, d320189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33372 q selected
    | true =>
      simp only [d46969, d320189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46970 q = 0) : d320190 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46970, d320190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46970, d320190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46971 q = 0) : d320191 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46971, d320191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46971, d320191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46972 q = 0) : d320192 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46972, d320192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46972, d320192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46973 q = 0) : d320193 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46973, d320193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46973, d320193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46986 q = 0) : d320206 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46986, d320206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46986, d320206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro33377 (p : Pattern) (selected : d46992 p = 0) : d320212 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46975 q = 0) : d320195 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46975, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33373 q selected
    | true =>
      simp only [d46975, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46976 q = 0) : d320196 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46976, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46976, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46977 q = 0) : d320197 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46977, d320197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46977, d320197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46978 q = 0) : d320198 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46978, d320198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46978, d320198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46981 q = 0) : d320201 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46981, d320201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46981, d320201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d46987 q = 0) : d320207 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46987, d320207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33376 q selected
    | true =>
      simp only [d46987, d320207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46988 q = 0) : d320208 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46988, d320208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46988, d320208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46989 q = 0) : d320209 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46989, d320209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46989, d320209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46990 q = 0) : d320210 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46990, d320210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d46990, d320210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d46991 q = 0) : d320211 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46991, d320211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46991, d320211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d46992 q = 0) : d320212 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46992, d320212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46992, d320212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro33378 (p : Pattern) (selected : d46999 p = 0) : d320219 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46983 q = 0) : d320203 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46983, d320203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33374 q selected
    | true =>
      simp only [d46983, d320203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33375 q selected
  have h2 (q : Pattern) (selected : d46984 q = 0) : d320204 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46984, d320204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46984, d320204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46985 q = 0) : d320205 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46985, d320205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46985, d320205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46993 q = 0) : d320213 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46993, d320213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33375 q selected
    | true =>
      simp only [d46993, d320213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33377 q selected
  have h5 (q : Pattern) (selected : d46994 q = 0) : d320214 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46994, d320214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46994, d320214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46995 q = 0) : d320215 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46995, d320215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46995, d320215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46996 q = 0) : d320216 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46996, d320216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46996, d320216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d46997 q = 0) : d320217 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46997, d320217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46997, d320217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d46998 q = 0) : d320218 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46998, d320218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d46998, d320218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46999 q = 0) : d320219 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46999, d320219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46999, d320219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro33379 (p : Pattern) (selected : d47003 p = 0) : d320223 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46993 q = 0) : d320213 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46993, d320213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33375 q selected
    | true =>
      simp only [d46993, d320213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33377 q selected
  have h2 (q : Pattern) (selected : d46994 q = 0) : d320214 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46994, d320214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46994, d320214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46995 q = 0) : d320215 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46995, d320215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46995, d320215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46997 q = 0) : d320217 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46997, d320217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46997, d320217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47002 q = 0) : d320222 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47002, d320222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47002, d320222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47003 q = 0) : d320223 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47003, d320223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47003, d320223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33380 (p : Pattern) (selected : d47009 p = 0) : d320229 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47000 q = 0) : d320220 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47000, d320220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33378 q selected
    | true =>
      simp only [d47000, d320220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47001 q = 0) : d320221 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47001, d320221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47001, d320221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47004 q = 0) : d320224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47004, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33379 q selected
    | true =>
      simp only [d47004, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47005 q = 0) : d320225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47005, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47005, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47006 q = 0) : d320226 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47006, d320226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47006, d320226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47007 q = 0) : d320227 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47007, d320227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47007, d320227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47008 q = 0) : d320228 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47008, d320228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47008, d320228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d47009 q = 0) : d320229 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47009, d320229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47009, d320229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33381 (p : Pattern) (selected : d47013 p = 0) : d320233 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47004 q = 0) : d320224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47004, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33379 q selected
    | true =>
      simp only [d47004, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47005 q = 0) : d320225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47005, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47005, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47010 q = 0) : d320230 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47010, d320230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47010, d320230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47011 q = 0) : d320231 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47011, d320231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47011, d320231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47012 q = 0) : d320232 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47012, d320232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47012, d320232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47013 q = 0) : d320233 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47013, d320233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47013, d320233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33382 (p : Pattern) (selected : d47016 p = 0) : d320284 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46877 q = 0) : d320195 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33353 q selected
    | true =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46878 q = 0) : d320196 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46879 q = 0) : d320197 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, d320197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46879, d320197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46880 q = 0) : d320198 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, d320198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46880, d320198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46881 q = 0) : d320199 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46881, d320199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46881, d320199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47016 q = 0) : d320284 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47016, d320284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47016, d320284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33383 (p : Pattern) (selected : d47022 p = 0) : d320290 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46885 q = 0) : d320203 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46885, d320203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33354 q selected
    | true =>
      simp only [d46885, d320203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33355 q selected
  have h2 (q : Pattern) (selected : d46886 q = 0) : d320204 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46886, d320204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46886, d320204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46887 q = 0) : d320205 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46887, d320205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46887, d320205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46895 q = 0) : d320213 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, d320213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33355 q selected
    | true =>
      simp only [d46895, d320213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33357 q selected
  have h5 (q : Pattern) (selected : d46896 q = 0) : d320214 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, d320214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46896, d320214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46897 q = 0) : d320215 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, d320215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46897, d320215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46898 q = 0) : d320216 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46898, d320216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46898, d320216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47017 q = 0) : d320285 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47017, d320285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33382 q selected
    | true =>
      simp only [d47017, d320285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d47018 q = 0) : d320286 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47018, d320286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47018, d320286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d47019 q = 0) : d320287 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47019, d320287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47019, d320287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47020 q = 0) : d320288 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47020, d320288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d47020, d320288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d47021 q = 0) : d320289 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47021, d320289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47021, d320289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d47022 q = 0) : d320290 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47022, d320290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d47022, d320290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro33384 (p : Pattern) (selected : d47028 p = 0) : d320296 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47023 q = 0) : d320291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47023, d320291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33383 q selected
    | true =>
      simp only [d47023, d320291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47024 q = 0) : d320292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47024, d320292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47024, d320292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47025 q = 0) : d320293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47025, d320293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47025, d320293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47026 q = 0) : d320294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47026, d320294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47026, d320294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47027 q = 0) : d320295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47027, d320295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47027, d320295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47028 q = 0) : d320296 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47028, d320296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47028, d320296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33385 (p : Pattern) (selected : d47034 p = 0) : d320302 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46939 q = 0) : d320257 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46939, d320257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33366 q selected
    | true =>
      simp only [d46939, d320257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33367 q selected
  have h2 (q : Pattern) (selected : d46940 q = 0) : d320258 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46940, d320258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46940, d320258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46941 q = 0) : d320259 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46941, d320259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46941, d320259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46942 q = 0) : d320260 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46942, d320260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46942, d320260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46949 q = 0) : d320267 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46949, d320267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33368 q selected
    | true =>
      simp only [d46949, d320267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33369 q selected
  have h6 (q : Pattern) (selected : d46950 q = 0) : d320268 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46950, d320268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46950, d320268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46951 q = 0) : d320269 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46951, d320269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46951, d320269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46964 q = 0) : d320282 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46964, d320282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33371 q selected
    | true =>
      simp only [d46964, d320282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33360 q selected
  have h9 (q : Pattern) (selected : d47014 q = 0) : d320234 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47014, d320234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33380 q selected
    | true =>
      simp only [d47014, d320234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33381 q selected
  have h10 (q : Pattern) (selected : d47015 q = 0) : d320283 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47015, d320283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d47015, d320283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47029 q = 0) : d320297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47029, d320297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33384 q selected
    | true =>
      simp only [d47029, d320297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d47030 q = 0) : d320298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47030, d320298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d47030, d320298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d47031 q = 0) : d320299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47031, d320299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d47031, d320299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d47032 q = 0) : d320300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47032, d320300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47032, d320300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d47033 q = 0) : d320301 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47033, d320301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47033, d320301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d47034 q = 0) : d320302 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47034, d320302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47034, d320302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro33386 (p : Pattern) (selected : d47035 p = 0) : d320303 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46902 q = 0) : d320220 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33358 q selected
    | true =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46903 q = 0) : d320221 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46906 q = 0) : d320224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33359 q selected
    | true =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46907 q = 0) : d320225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46908 q = 0) : d320226 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, d320226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46908, d320226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46909 q = 0) : d320227 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, d320227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46909, d320227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46935 q = 0) : d320253 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46935, d320253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46935, d320253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47035 q = 0) : d320303 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47035, d320303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47035, d320303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33387 (p : Pattern) (selected : d47036 p = 0) : d320304 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46906 q = 0) : d320224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33359 q selected
    | true =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46907 q = 0) : d320225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46912 q = 0) : d320230 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, d320230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46912, d320230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46913 q = 0) : d320231 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46913, d320231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46913, d320231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46937 q = 0) : d320255 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46937, d320255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46937, d320255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47036 q = 0) : d320304 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47036, d320304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47036, d320304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33388 (p : Pattern) (selected : d47041 p = 0) : d320309 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46902 q = 0) : d320220 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33358 q selected
    | true =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46903 q = 0) : d320221 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46906 q = 0) : d320224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33359 q selected
    | true =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46907 q = 0) : d320225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46908 q = 0) : d320226 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, d320226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46908, d320226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46943 q = 0) : d320261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46943, d320261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46943, d320261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46944 q = 0) : d320262 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46944, d320262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46944, d320262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d47041 q = 0) : d320309 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47041, d320309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47041, d320309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33389 (p : Pattern) (selected : d47042 p = 0) : d320310 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46906 q = 0) : d320224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33359 q selected
    | true =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46907 q = 0) : d320225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46912 q = 0) : d320230 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, d320230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46912, d320230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46946 q = 0) : d320264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46946, d320264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46946, d320264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46947 q = 0) : d320265 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46947, d320265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d46947, d320265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47042 q = 0) : d320310 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47042, d320310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47042, d320310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33390 (p : Pattern) (selected : d47046 p = 0) : d320314 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46958 q = 0) : d320276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46958, d320276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33370 q selected
    | true =>
      simp only [d46958, d320276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d46959 q = 0) : d320277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46959, d320277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46959, d320277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46902 q = 0) : d320220 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33358 q selected
    | true =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46903 q = 0) : d320221 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46960 q = 0) : d320278 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46960, d320278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46960, d320278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46961 q = 0) : d320279 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46961, d320279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46961, d320279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d46962 q = 0) : d320280 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46962, d320280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46962, d320280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d47046 q = 0) : d320314 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47046, d320314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47046, d320314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33391 (p : Pattern) (selected : d47048 p = 0) : d320242 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47000 q = 0) : d320220 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47000, d320220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33378 q selected
    | true =>
      simp only [d47000, d320220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47001 q = 0) : d320221 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47001, d320221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47001, d320221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47004 q = 0) : d320224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47004, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33379 q selected
    | true =>
      simp only [d47004, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47005 q = 0) : d320225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47005, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47005, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47006 q = 0) : d320226 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47006, d320226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47006, d320226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47007 q = 0) : d320227 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47007, d320227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47007, d320227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47008 q = 0) : d320228 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47008, d320228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47008, d320228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d47048 q = 0) : d320242 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47048, d320242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47048, d320242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33392 (p : Pattern) (selected : d47049 p = 0) : d320243 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47004 q = 0) : d320224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47004, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33379 q selected
    | true =>
      simp only [d47004, d320224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47005 q = 0) : d320225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47005, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47005, d320225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47010 q = 0) : d320230 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47010, d320230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47010, d320230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47011 q = 0) : d320231 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47011, d320231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47011, d320231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47012 q = 0) : d320232 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47012, d320232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47012, d320232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47049 q = 0) : d320243 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47049, d320243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47049, d320243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33393 (p : Pattern) (selected : d47052 p = 0) : d320317 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47023 q = 0) : d320291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47023, d320291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33383 q selected
    | true =>
      simp only [d47023, d320291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47024 q = 0) : d320292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47024, d320292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47024, d320292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47025 q = 0) : d320293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47025, d320293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47025, d320293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47026 q = 0) : d320294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47026, d320294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47026, d320294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47027 q = 0) : d320295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47027, d320295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47027, d320295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47052 q = 0) : d320317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47052, d320317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47052, d320317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33394 (p : Pattern) (selected : d47058 p = 0) : d320323 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46939 q = 0) : d320257 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46939, d320257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33366 q selected
    | true =>
      simp only [d46939, d320257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33367 q selected
  have h2 (q : Pattern) (selected : d46940 q = 0) : d320258 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46940, d320258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46940, d320258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46941 q = 0) : d320259 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46941, d320259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46941, d320259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46942 q = 0) : d320260 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46942, d320260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46942, d320260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46949 q = 0) : d320267 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46949, d320267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33368 q selected
    | true =>
      simp only [d46949, d320267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33369 q selected
  have h6 (q : Pattern) (selected : d46950 q = 0) : d320268 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46950, d320268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46950, d320268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46951 q = 0) : d320269 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46951, d320269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46951, d320269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d46964 q = 0) : d320282 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46964, d320282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33371 q selected
    | true =>
      simp only [d46964, d320282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33360 q selected
  have h9 (q : Pattern) (selected : d47014 q = 0) : d320234 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47014, d320234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33380 q selected
    | true =>
      simp only [d47014, d320234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33381 q selected
  have h10 (q : Pattern) (selected : d47015 q = 0) : d320283 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47015, d320283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d47015, d320283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47029 q = 0) : d320297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47029, d320297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33384 q selected
    | true =>
      simp only [d47029, d320297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d47030 q = 0) : d320298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47030, d320298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d47030, d320298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d47031 q = 0) : d320299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47031, d320299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d47031, d320299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d47032 q = 0) : d320300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47032, d320300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47032, d320300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d47033 q = 0) : d320301 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47033, d320301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47033, d320301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d47037 q = 0) : d320305 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47037, d320305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33386 q selected
    | true =>
      simp only [d47037, d320305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33387 q selected
  have h17 (q : Pattern) (selected : d47038 q = 0) : d320306 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47038, d320306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47038, d320306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d47039 q = 0) : d320307 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47039, d320307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d47039, d320307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d47040 q = 0) : d320308 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47040, d320308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47040, d320308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d47043 q = 0) : d320311 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47043, d320311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33388 q selected
    | true =>
      simp only [d47043, d320311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33389 q selected
  have h21 (q : Pattern) (selected : d47044 q = 0) : d320312 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47044, d320312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47044, d320312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d47045 q = 0) : d320313 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47045, d320313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d47045, d320313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d47047 q = 0) : d320315 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47047, d320315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33390 q selected
    | true =>
      simp only [d47047, d320315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33363 q selected
  have h24 (q : Pattern) (selected : d47050 q = 0) : d320244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47050, d320244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33391 q selected
    | true =>
      simp only [d47050, d320244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33392 q selected
  have h25 (q : Pattern) (selected : d47051 q = 0) : d320316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47051, d320316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d47051, d320316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d47053 q = 0) : d320318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47053, d320318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33393 q selected
    | true =>
      simp only [d47053, d320318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d47054 q = 0) : d320319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47054, d320319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d47054, d320319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d47055 q = 0) : d320320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47055, d320320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d47055, d320320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d47056 q = 0) : d320321 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47056, d320321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d47056, d320321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d47057 q = 0) : d320322 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47057, d320322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d47057, d320322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d47058 q = 0) : d320323 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47058, d320323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d47058, d320323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro33395 (p : Pattern) (selected : d47065 p = 0) : d320330 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46916 q = 0) : d320234 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46916, d320234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33360 q selected
    | true =>
      simp only [d46916, d320234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33361 q selected
  have h2 (q : Pattern) (selected : d46917 q = 0) : d320235 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, d320235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46917, d320235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d46918 q = 0) : d320236 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, d320236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46918, d320236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46919 q = 0) : d320237 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, d320237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46919, d320237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d46920 q = 0) : d320238 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, d320238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46920, d320238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47060 q = 0) : d320325 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47060, d320325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33361 q selected
    | true =>
      simp only [d47060, d320325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47061 q = 0) : d320326 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47061, d320326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47061, d320326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47062 q = 0) : d320327 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47062, d320327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47062, d320327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d47063 q = 0) : d320328 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47063, d320328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47063, d320328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d47064 q = 0) : d320329 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47064, d320329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47064, d320329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47065 q = 0) : d320330 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47065, d320330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47065, d320330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro33396 (p : Pattern) (selected : d47071 p = 0) : d320336 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47060 q = 0) : d320325 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47060, d320325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33361 q selected
    | true =>
      simp only [d47060, d320325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47061 q = 0) : d320326 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47061, d320326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47061, d320326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47062 q = 0) : d320327 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47062, d320327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47062, d320327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47063 q = 0) : d320328 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47063, d320328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47063, d320328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47064 q = 0) : d320329 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47064, d320329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47064, d320329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47066 q = 0) : d320331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47066, d320331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33364 q selected
    | true =>
      simp only [d47066, d320331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47067 q = 0) : d320332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47067, d320332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47067, d320332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47068 q = 0) : d320333 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47068, d320333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47068, d320333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d47069 q = 0) : d320334 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47069, d320334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47069, d320334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d47070 q = 0) : d320335 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47070, d320335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47070, d320335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47071 q = 0) : d320336 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47071, d320336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47071, d320336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro33397 (p : Pattern) (selected : d47078 p = 0) : d320343 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47047 q = 0) : d320315 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47047, d320315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33390 q selected
    | true =>
      simp only [d47047, d320315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33363 q selected
  have h2 (q : Pattern) (selected : d47050 q = 0) : d320244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47050, d320244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33391 q selected
    | true =>
      simp only [d47050, d320244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33392 q selected
  have h3 (q : Pattern) (selected : d47051 q = 0) : d320316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47051, d320316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47051, d320316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47053 q = 0) : d320318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47053, d320318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33393 q selected
    | true =>
      simp only [d47053, d320318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47054 q = 0) : d320319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47054, d320319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47054, d320319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47055 q = 0) : d320320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47055, d320320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47055, d320320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d47076 q = 0) : d320341 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47076, d320341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47076, d320341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47077 q = 0) : d320342 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47077, d320342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47077, d320342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d47078 q = 0) : d320343 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47078, d320343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47078, d320343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro33398 (p : Pattern) (selected : d47080 p = 0) : d320345 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47066 q = 0) : d320331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47066, d320331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33364 q selected
    | true =>
      simp only [d47066, d320331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47067 q = 0) : d320332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47067, d320332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47067, d320332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47068 q = 0) : d320333 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47068, d320333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47068, d320333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47069 q = 0) : d320334 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47069, d320334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47069, d320334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47070 q = 0) : d320335 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47070, d320335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47070, d320335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47080 q = 0) : d320345 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47080, d320345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47080, d320345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33399 (p : Pattern) (selected : d47091 p = 0) : d320356 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47086 q = 0) : d320351 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, d320351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47086, d320351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33353 q selected
  have h2 (q : Pattern) (selected : d46877 q = 0) : d320195 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33353 q selected
    | true =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47087 q = 0) : d320352 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, d320352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47087, d320352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46878 q = 0) : d320196 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47088 q = 0) : d320353 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, d320353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47088, d320353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47089 q = 0) : d320354 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, d320354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47089, d320354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47090 q = 0) : d320355 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47090, d320355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47090, d320355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47091 q = 0) : d320356 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47091, d320356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47091, d320356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33400 (p : Pattern) (selected : d47096 p = 0) : d320361 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47086 q = 0) : d320351 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, d320351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47086, d320351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33353 q selected
  have h2 (q : Pattern) (selected : d46877 q = 0) : d320195 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33353 q selected
    | true =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47087 q = 0) : d320352 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, d320352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47087, d320352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46878 q = 0) : d320196 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47088 q = 0) : d320353 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, d320353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47088, d320353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47089 q = 0) : d320354 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, d320354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47089, d320354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47090 q = 0) : d320355 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47090, d320355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47090, d320355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47095 q = 0) : d320360 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47095, d320360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47095, d320360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d47096 q = 0) : d320361 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47096, d320361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47096, d320361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro33401 (p : Pattern) (selected : d47106 p = 0) : d320371 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47086 q = 0) : d320351 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, d320351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47086, d320351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33353 q selected
  have h2 (q : Pattern) (selected : d46877 q = 0) : d320195 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33353 q selected
    | true =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47087 q = 0) : d320352 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, d320352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47087, d320352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46878 q = 0) : d320196 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47088 q = 0) : d320353 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, d320353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47088, d320353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47089 q = 0) : d320354 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, d320354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47089, d320354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47095 q = 0) : d320360 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47095, d320360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47095, d320360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d47101 q = 0) : d320366 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47101, d320366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47101, d320366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33356 q selected
  have h9 (q : Pattern) (selected : d46889 q = 0) : d320207 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46889, d320207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33356 q selected
    | true =>
      simp only [d46889, d320207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d47102 q = 0) : d320367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47102, d320367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d47102, d320367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46890 q = 0) : d320208 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46890, d320208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46890, d320208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d47103 q = 0) : d320368 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47103, d320368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d47103, d320368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d47104 q = 0) : d320369 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47104, d320369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d47104, d320369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d47105 q = 0) : d320370 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47105, d320370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d47105, d320370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d47106 q = 0) : d320371 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47106, d320371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47106, d320371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro33402 (p : Pattern) (selected : d47112 p = 0) : d320377 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47092 q = 0) : d320357 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47092, d320357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47092, d320357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33399 q selected
  have h2 (q : Pattern) (selected : d47093 q = 0) : d320358 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47093, d320358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47093, d320358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47094 q = 0) : d320359 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47094, d320359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47094, d320359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47097 q = 0) : d320362 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47097, d320362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33399 q selected
    | true =>
      simp only [d47097, d320362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33400 q selected
  have h5 (q : Pattern) (selected : d47098 q = 0) : d320363 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47098, d320363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47098, d320363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47099 q = 0) : d320364 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47099, d320364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47099, d320364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d47100 q = 0) : d320365 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47100, d320365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47100, d320365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47107 q = 0) : d320372 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, d320372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33400 q selected
    | true =>
      simp only [d47107, d320372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33401 q selected
  have h9 (q : Pattern) (selected : d47108 q = 0) : d320373 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, d320373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47108, d320373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d47109 q = 0) : d320374 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, d320374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47109, d320374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47110 q = 0) : d320375 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47110, d320375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47110, d320375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d47111 q = 0) : d320376 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47111, d320376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47111, d320376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d47112 q = 0) : d320377 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47112, d320377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d47112, d320377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro33403 (p : Pattern) (selected : d47117 p = 0) : d320382 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47097 q = 0) : d320362 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47097, d320362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33399 q selected
    | true =>
      simp only [d47097, d320362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33400 q selected
  have h2 (q : Pattern) (selected : d47098 q = 0) : d320363 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47098, d320363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47098, d320363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47099 q = 0) : d320364 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47099, d320364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47099, d320364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47107 q = 0) : d320372 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, d320372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33400 q selected
    | true =>
      simp only [d47107, d320372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33401 q selected
  have h5 (q : Pattern) (selected : d47108 q = 0) : d320373 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, d320373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47108, d320373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47109 q = 0) : d320374 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, d320374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47109, d320374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d47110 q = 0) : d320375 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47110, d320375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47110, d320375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47115 q = 0) : d320380 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47115, d320380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47115, d320380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d47116 q = 0) : d320381 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47116, d320381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47116, d320381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d47117 q = 0) : d320382 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47117, d320382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d47117, d320382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro33404 (p : Pattern) (selected : d47123 p = 0) : d320388 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47113 q = 0) : d320378 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47113, d320378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33402 q selected
    | true =>
      simp only [d47113, d320378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47114 q = 0) : d320379 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47114, d320379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47114, d320379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47118 q = 0) : d320383 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47118, d320383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33403 q selected
    | true =>
      simp only [d47118, d320383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47119 q = 0) : d320384 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47119, d320384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47119, d320384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47120 q = 0) : d320385 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47120, d320385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47120, d320385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47121 q = 0) : d320386 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47121, d320386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47121, d320386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47122 q = 0) : d320387 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47122, d320387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47122, d320387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d47123 q = 0) : d320388 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47123, d320388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47123, d320388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33405 (p : Pattern) (selected : d47125 p = 0) : d320390 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47107 q = 0) : d320372 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, d320372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33400 q selected
    | true =>
      simp only [d47107, d320372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33401 q selected
  have h2 (q : Pattern) (selected : d47108 q = 0) : d320373 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, d320373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47108, d320373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47109 q = 0) : d320374 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, d320374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47109, d320374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47115 q = 0) : d320380 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47115, d320380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47115, d320380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47124 q = 0) : d320389 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47124, d320389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47124, d320389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47125 q = 0) : d320390 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47125, d320390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47125, d320390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33406 (p : Pattern) (selected : d47131 p = 0) : d320396 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47118 q = 0) : d320383 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47118, d320383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33403 q selected
    | true =>
      simp only [d47118, d320383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47119 q = 0) : d320384 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47119, d320384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47119, d320384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47126 q = 0) : d320391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47126, d320391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33405 q selected
    | true =>
      simp only [d47126, d320391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47127 q = 0) : d320392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47127, d320392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47127, d320392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47128 q = 0) : d320393 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47128, d320393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47128, d320393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47129 q = 0) : d320394 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47129, d320394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47129, d320394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47130 q = 0) : d320395 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47130, d320395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47130, d320395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d47131 q = 0) : d320396 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47131, d320396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47131, d320396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33407 (p : Pattern) (selected : d47138 p = 0) : d320356 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47133 q = 0) : d320351 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47133, d320351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47133, d320351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33373 q selected
  have h2 (q : Pattern) (selected : d46975 q = 0) : d320195 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46975, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33373 q selected
    | true =>
      simp only [d46975, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47134 q = 0) : d320352 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47134, d320352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47134, d320352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46976 q = 0) : d320196 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46976, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46976, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47135 q = 0) : d320353 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47135, d320353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47135, d320353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47136 q = 0) : d320354 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47136, d320354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47136, d320354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47137 q = 0) : d320355 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47137, d320355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47137, d320355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47138 q = 0) : d320356 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47138, d320356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47138, d320356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33408 (p : Pattern) (selected : d47140 p = 0) : d320361 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47133 q = 0) : d320351 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47133, d320351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47133, d320351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33373 q selected
  have h2 (q : Pattern) (selected : d46975 q = 0) : d320195 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46975, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33373 q selected
    | true =>
      simp only [d46975, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47134 q = 0) : d320352 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47134, d320352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47134, d320352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46976 q = 0) : d320196 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46976, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46976, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47135 q = 0) : d320353 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47135, d320353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47135, d320353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47136 q = 0) : d320354 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47136, d320354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47136, d320354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47137 q = 0) : d320355 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47137, d320355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47137, d320355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47139 q = 0) : d320360 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47139, d320360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47139, d320360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d47140 q = 0) : d320361 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47140, d320361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47140, d320361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro33409 (p : Pattern) (selected : d47149 p = 0) : d320371 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47133 q = 0) : d320351 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47133, d320351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47133, d320351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33373 q selected
  have h2 (q : Pattern) (selected : d46975 q = 0) : d320195 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46975, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33373 q selected
    | true =>
      simp only [d46975, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47134 q = 0) : d320352 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47134, d320352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47134, d320352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46976 q = 0) : d320196 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46976, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46976, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47135 q = 0) : d320353 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47135, d320353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47135, d320353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47136 q = 0) : d320354 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47136, d320354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47136, d320354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47139 q = 0) : d320360 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47139, d320360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47139, d320360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d47144 q = 0) : d320366 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47144, d320366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47144, d320366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33376 q selected
  have h9 (q : Pattern) (selected : d46987 q = 0) : d320207 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46987, d320207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33376 q selected
    | true =>
      simp only [d46987, d320207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d47145 q = 0) : d320367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47145, d320367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d47145, d320367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d46988 q = 0) : d320208 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46988, d320208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d46988, d320208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d47146 q = 0) : d320368 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47146, d320368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d47146, d320368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d47147 q = 0) : d320369 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47147, d320369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d47147, d320369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d47148 q = 0) : d320370 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47148, d320370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d47148, d320370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d47149 q = 0) : d320371 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47149, d320371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47149, d320371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro33410 (p : Pattern) (selected : d47156 p = 0) : d320382 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47141 q = 0) : d320362 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47141, d320362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33407 q selected
    | true =>
      simp only [d47141, d320362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33408 q selected
  have h2 (q : Pattern) (selected : d47142 q = 0) : d320363 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47142, d320363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47142, d320363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47143 q = 0) : d320364 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47143, d320364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47143, d320364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47150 q = 0) : d320372 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47150, d320372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33408 q selected
    | true =>
      simp only [d47150, d320372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33409 q selected
  have h5 (q : Pattern) (selected : d47151 q = 0) : d320373 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47151, d320373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47151, d320373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47152 q = 0) : d320374 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47152, d320374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47152, d320374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d47153 q = 0) : d320375 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47153, d320375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47153, d320375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47154 q = 0) : d320380 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47154, d320380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47154, d320380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d47155 q = 0) : d320381 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47155, d320381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47155, d320381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d47156 q = 0) : d320382 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47156, d320382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d47156, d320382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro33411 (p : Pattern) (selected : d47160 p = 0) : d320390 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47150 q = 0) : d320372 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47150, d320372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33408 q selected
    | true =>
      simp only [d47150, d320372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33409 q selected
  have h2 (q : Pattern) (selected : d47151 q = 0) : d320373 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47151, d320373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47151, d320373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47152 q = 0) : d320374 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47152, d320374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47152, d320374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47154 q = 0) : d320380 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47154, d320380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47154, d320380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47159 q = 0) : d320389 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47159, d320389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47159, d320389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47160 q = 0) : d320390 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47160, d320390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47160, d320390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33412 (p : Pattern) (selected : d47166 p = 0) : d320396 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47157 q = 0) : d320383 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47157, d320383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33410 q selected
    | true =>
      simp only [d47157, d320383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47158 q = 0) : d320384 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47158, d320384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47158, d320384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47161 q = 0) : d320391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47161, d320391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33411 q selected
    | true =>
      simp only [d47161, d320391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47162 q = 0) : d320392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47162, d320392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47162, d320392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47163 q = 0) : d320393 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47163, d320393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47163, d320393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47164 q = 0) : d320394 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47164, d320394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47164, d320394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47165 q = 0) : d320395 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47165, d320395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47165, d320395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d47166 q = 0) : d320396 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47166, d320396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47166, d320396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33413 (p : Pattern) (selected : d47172 p = 0) : d320403 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47167 q = 0) : d320398 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d47167, d320398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro27636 q selected
    | true =>
      simp only [d47167, d320398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33372 q selected
  have h2 (q : Pattern) (selected : d47168 q = 0) : d320399 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d47168, d320399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47168, d320399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47169 q = 0) : d320400 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d47169, d320400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47169, d320400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46969 q = 0) : d320189 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46969, d320189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33372 q selected
    | true =>
      simp only [d46969, d320189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46970 q = 0) : d320190 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46970, d320190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46970, d320190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46971 q = 0) : d320191 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46971, d320191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d46971, d320191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47170 q = 0) : d320401 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d47170, d320401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47170, d320401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47171 q = 0) : d320402 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d47171, d320402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47171, d320402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d47172 q = 0) : d320403 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d47172, d320403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d47172, d320403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro33414 (p : Pattern) (selected : d47178 p = 0) : d320409 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47133 q = 0) : d320351 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47133, d320351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47133, d320351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33373 q selected
  have h2 (q : Pattern) (selected : d46975 q = 0) : d320195 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46975, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33373 q selected
    | true =>
      simp only [d46975, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47134 q = 0) : d320352 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47134, d320352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47134, d320352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46976 q = 0) : d320196 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46976, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46976, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47135 q = 0) : d320353 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47135, d320353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47135, d320353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47136 q = 0) : d320354 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47136, d320354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47136, d320354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47139 q = 0) : d320360 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47139, d320360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47139, d320360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d47144 q = 0) : d320366 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47144, d320366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47144, d320366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33376 q selected
  have h9 (q : Pattern) (selected : d46987 q = 0) : d320207 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46987, d320207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33376 q selected
    | true =>
      simp only [d46987, d320207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d47145 q = 0) : d320367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47145, d320367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d47145, d320367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47173 q = 0) : d320404 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47173, d320404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33413 q selected
    | true =>
      simp only [d47173, d320404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d47174 q = 0) : d320405 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47174, d320405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d47174, d320405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d47175 q = 0) : d320406 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47175, d320406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d47175, d320406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d47176 q = 0) : d320407 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47176, d320407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d47176, d320407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d47177 q = 0) : d320408 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47177, d320408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d47177, d320408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d47178 q = 0) : d320409 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47178, d320409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47178, d320409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro33415 (p : Pattern) (selected : d47184 p = 0) : d320415 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47179 q = 0) : d320410 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47179, d320410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33408 q selected
    | true =>
      simp only [d47179, d320410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33414 q selected
  have h2 (q : Pattern) (selected : d47180 q = 0) : d320411 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47180, d320411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47180, d320411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47181 q = 0) : d320412 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47181, d320412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47181, d320412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47182 q = 0) : d320413 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47182, d320413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47182, d320413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47183 q = 0) : d320414 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47183, d320414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47183, d320414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47184 q = 0) : d320415 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47184, d320415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47184, d320415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33416 (p : Pattern) (selected : d47190 p = 0) : d320421 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47185 q = 0) : d320416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47185, d320416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33415 q selected
    | true =>
      simp only [d47185, d320416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47186 q = 0) : d320417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47186, d320417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47186, d320417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47187 q = 0) : d320418 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47187, d320418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47187, d320418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47188 q = 0) : d320419 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47188, d320419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47188, d320419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47189 q = 0) : d320420 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47189, d320420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47189, d320420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47190 q = 0) : d320421 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47190, d320421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47190, d320421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33417 (p : Pattern) (selected : d47193 p = 0) : d320424 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47086 q = 0) : d320351 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, d320351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47086, d320351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33353 q selected
  have h2 (q : Pattern) (selected : d46877 q = 0) : d320195 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33353 q selected
    | true =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47087 q = 0) : d320352 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, d320352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47087, d320352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46878 q = 0) : d320196 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47088 q = 0) : d320353 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, d320353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47088, d320353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47089 q = 0) : d320354 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, d320354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47089, d320354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d47090 q = 0) : d320355 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47090, d320355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47090, d320355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47193 q = 0) : d320424 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47193, d320424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47193, d320424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33418 (p : Pattern) (selected : d47199 p = 0) : d320430 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47097 q = 0) : d320362 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47097, d320362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33399 q selected
    | true =>
      simp only [d47097, d320362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33400 q selected
  have h2 (q : Pattern) (selected : d47098 q = 0) : d320363 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47098, d320363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47098, d320363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47099 q = 0) : d320364 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47099, d320364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47099, d320364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47107 q = 0) : d320372 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, d320372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33400 q selected
    | true =>
      simp only [d47107, d320372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33401 q selected
  have h5 (q : Pattern) (selected : d47108 q = 0) : d320373 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, d320373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47108, d320373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47109 q = 0) : d320374 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, d320374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47109, d320374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d47110 q = 0) : d320375 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47110, d320375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47110, d320375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47194 q = 0) : d320425 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47194, d320425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33417 q selected
    | true =>
      simp only [d47194, d320425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d47195 q = 0) : d320426 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47195, d320426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47195, d320426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d47196 q = 0) : d320427 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47196, d320427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47196, d320427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47197 q = 0) : d320428 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47197, d320428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d47197, d320428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d47198 q = 0) : d320429 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47198, d320429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47198, d320429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d47199 q = 0) : d320430 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47199, d320430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d47199, d320430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro33419 (p : Pattern) (selected : d47205 p = 0) : d320436 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47200 q = 0) : d320431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47200, d320431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33418 q selected
    | true =>
      simp only [d47200, d320431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47201 q = 0) : d320432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47201, d320432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47201, d320432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47202 q = 0) : d320433 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47202, d320433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47202, d320433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47203 q = 0) : d320434 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47203, d320434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47203, d320434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47204 q = 0) : d320435 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47204, d320435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47204, d320435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47205 q = 0) : d320436 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47205, d320436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47205, d320436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33420 (p : Pattern) (selected : d47211 p = 0) : d320442 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47132 q = 0) : d320397 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47132, d320397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33404 q selected
    | true =>
      simp only [d47132, d320397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33406 q selected
  have h2 (q : Pattern) (selected : d47191 q = 0) : d320422 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47191, d320422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33412 q selected
    | true =>
      simp only [d47191, d320422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33416 q selected
  have h3 (q : Pattern) (selected : d47192 q = 0) : d320423 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47192, d320423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47192, d320423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47206 q = 0) : d320437 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47206, d320437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33419 q selected
    | true =>
      simp only [d47206, d320437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47207 q = 0) : d320438 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47207, d320438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47207, d320438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47208 q = 0) : d320439 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47208, d320439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47208, d320439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d47209 q = 0) : d320440 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47209, d320440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47209, d320440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d47210 q = 0) : d320441 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47210, d320441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47210, d320441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d47211 q = 0) : d320442 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47211, d320442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47211, d320442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro33421 (p : Pattern) (selected : d47216 p = 0) : d320447 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47126 q = 0) : d320391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47126, d320391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33405 q selected
    | true =>
      simp only [d47126, d320391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47127 q = 0) : d320392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47127, d320392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47127, d320392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47213 q = 0) : d320444 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47213, d320444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47213, d320444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47214 q = 0) : d320445 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47214, d320445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47214, d320445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47215 q = 0) : d320446 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47215, d320446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47215, d320446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47216 q = 0) : d320447 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47216, d320447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47216, d320447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33422 (p : Pattern) (selected : d47222 p = 0) : d320453 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47217 q = 0) : d320448 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47217, d320448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33421 q selected
    | true =>
      simp only [d47217, d320448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47218 q = 0) : d320449 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47218, d320449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47218, d320449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47219 q = 0) : d320450 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47219, d320450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47219, d320450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47220 q = 0) : d320451 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47220, d320451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47220, d320451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47221 q = 0) : d320452 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47221, d320452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47221, d320452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47222 q = 0) : d320453 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47222, d320453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47222, d320453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33423 (p : Pattern) (selected : d47228 p = 0) : d320459 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d46922 q = 0) : d320240 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46922, d320240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46922, d320240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33362 q selected
  have h2 (q : Pattern) (selected : d46923 q = 0) : d320241 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46923, d320241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46923, d320241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d46932 q = 0) : d320250 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46932, d320250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33362 q selected
    | true =>
      simp only [d46932, d320250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33365 q selected
  have h4 (q : Pattern) (selected : d46933 q = 0) : d320251 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46933, d320251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46933, d320251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d46934 q = 0) : d320252 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46934, d320252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d46934, d320252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47059 q = 0) : d320324 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d47059, d320324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33385 q selected
    | true =>
      simp only [d47059, d320324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33394 q selected
  have h7 (q : Pattern) (selected : d47072 q = 0) : d320337 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d47072, d320337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33395 q selected
    | true =>
      simp only [d47072, d320337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33396 q selected
  have h8 (q : Pattern) (selected : d47073 q = 0) : d320338 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d47073, d320338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47073, d320338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d47074 q = 0) : d320339 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d47074, d320339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d47074, d320339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d47075 q = 0) : d320340 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d47075, d320340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47075, d320340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47079 q = 0) : d320344 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d47079, d320344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47079, d320344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33397 q selected
  have h12 (q : Pattern) (selected : d47081 q = 0) : d320346 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d47081, d320346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47081, d320346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33398 q selected
  have h13 (q : Pattern) (selected : d47082 q = 0) : d320347 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d47082, d320347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d47082, d320347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d47083 q = 0) : d320348 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d47083, d320348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d47083, d320348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d47084 q = 0) : d320349 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d47084, d320349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d47084, d320349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d47085 q = 0) : d320350 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d47085, d320350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d47085, d320350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d47212 q = 0) : d320443 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d47212, d320443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47212, d320443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33420 q selected
  have h18 (q : Pattern) (selected : d47223 q = 0) : d320454 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d47223, d320454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47223, d320454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33422 q selected
  have h19 (q : Pattern) (selected : d47224 q = 0) : d320455 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d47224, d320455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d47224, d320455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d47225 q = 0) : d320456 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d47225, d320456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d47225, d320456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d47226 q = 0) : d320457 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d47226, d320457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d47226, d320457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d47227 q = 0) : d320458 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d47227, d320458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d47227, d320458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d47228 q = 0) : d320459 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d47228, d320459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d47228, d320459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro33424 (p : Pattern) (selected : d47234 p = 0) : d320465 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47229 q = 0) : d320460 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d47229, d320460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47229, d320460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33423 q selected
  have h2 (q : Pattern) (selected : d47230 q = 0) : d320461 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d47230, d320461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47230, d320461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47231 q = 0) : d320462 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d47231, d320462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47231, d320462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47232 q = 0) : d320463 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d47232, d320463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47232, d320463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47233 q = 0) : d320464 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d47233, d320464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47233, d320464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d47234 q = 0) : d320465 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d47234, d320465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47234, d320465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33425 (p : Pattern) (selected : d47240 p = 0) : d320471 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 0) : d319211 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d319211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33045 q selected
    | true =>
      simp only [d45496, d319211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33107 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d45903 q = 0) : d319500 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45903, d319500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45903, d319500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33184 q selected
  have h3 (q : Pattern) (selected : d45904 q = 0) : d319501 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d45904, d319501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45904, d319501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46456 q = 0) : d319887 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d46456, d319887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46456, d319887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33272 q selected
  have h5 (q : Pattern) (selected : d46457 q = 0) : d319888 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d46457, d319888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46457, d319888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46458 q = 0) : d319889 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d46458, d319889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46458, d319889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d46860 q = 0) : d320181 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d46860, d320181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46860, d320181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33351 q selected
  have h8 (q : Pattern) (selected : d46861 q = 0) : d320182 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d46861, d320182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46861, d320182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d46862 q = 0) : d320183 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d46862, d320183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46862, d320183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d46863 q = 0) : d320184 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d46863, d320184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d46863, d320184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d47235 q = 0) : d320466 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d47235, d320466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47235, d320466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33424 q selected
  have h12 (q : Pattern) (selected : d47236 q = 0) : d320467 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d47236, d320467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47236, d320467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d47237 q = 0) : d320468 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d47237, d320468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47237, d320468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d47238 q = 0) : d320469 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47238, d320469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47238, d320469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d47239 q = 0) : d320470 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47239, d320470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d47239, d320470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d47240 q = 0) : d320471 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47240, d320471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d47240, d320471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro33426 (p : Pattern) (selected : d47246 p = 0) : d320477 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47241 q = 0) : d320472 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47241, d320472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33425 q selected
    | true =>
      simp only [d47241, d320472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47242 q = 0) : d320473 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47242, d320473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47242, d320473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47243 q = 0) : d320474 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47243, d320474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47243, d320474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47244 q = 0) : d320475 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47244, d320475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47244, d320475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47245 q = 0) : d320476 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47245, d320476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47245, d320476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47246 q = 0) : d320477 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47246, d320477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47246, d320477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33427 (p : Pattern) (selected : d47252 p = 0) : d320483 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47247 q = 0) : d320478 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47247, d320478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33426 q selected
    | true =>
      simp only [d47247, d320478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47248 q = 0) : d320479 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47248, d320479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47248, d320479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47249 q = 0) : d320480 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47249, d320480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47249, d320480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47250 q = 0) : d320481 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47250, d320481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47250, d320481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47251 q = 0) : d320482 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47251, d320482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47251, d320482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47252 q = 0) : d320483 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47252, d320483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47252, d320483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33428 (p : Pattern) (selected : d47258 p = 0) : d320489 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47253 q = 0) : d320484 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47253, d320484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33427 q selected
    | true =>
      simp only [d47253, d320484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47254 q = 0) : d320485 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47254, d320485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47254, d320485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47255 q = 0) : d320486 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47255, d320486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47255, d320486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47256 q = 0) : d320487 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47256, d320487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47256, d320487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47257 q = 0) : d320488 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47257, d320488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47257, d320488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47258 q = 0) : d320489 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47258, d320489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47258, d320489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33429 (p : Pattern) (selected : d47264 p = 0) : d320495 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47259 q = 0) : d320490 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47259, d320490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33428 q selected
    | true =>
      simp only [d47259, d320490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47260 q = 0) : d320491 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47260, d320491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47260, d320491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47261 q = 0) : d320492 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47261, d320492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47261, d320492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47262 q = 0) : d320493 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47262, d320493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47262, d320493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47263 q = 0) : d320494 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47263, d320494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47263, d320494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47264 q = 0) : d320495 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47264, d320495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47264, d320495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33430 (p : Pattern) (selected : d47270 p = 0) : d320501 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47265 q = 0) : d320496 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47265, d320496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33429 q selected
    | true =>
      simp only [d47265, d320496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47266 q = 0) : d320497 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47266, d320497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47266, d320497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47267 q = 0) : d320498 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47267, d320498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47267, d320498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47268 q = 0) : d320499 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47268, d320499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47268, d320499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47269 q = 0) : d320500 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47269, d320500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47269, d320500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47270 q = 0) : d320501 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47270, d320501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47270, d320501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33431 (p : Pattern) (selected : d47276 p = 0) : d320507 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47271 q = 0) : d320502 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47271, d320502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33430 q selected
    | true =>
      simp only [d47271, d320502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47272 q = 0) : d320503 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47272, d320503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47272, d320503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47273 q = 0) : d320504 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47273, d320504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47273, d320504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47274 q = 0) : d320505 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47274, d320505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47274, d320505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47275 q = 0) : d320506 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47275, d320506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47275, d320506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47276 q = 0) : d320507 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47276, d320507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47276, d320507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33432 (p : Pattern) (selected : d47282 p = 0) : d320513 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47277 q = 0) : d320508 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47277, d320508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33431 q selected
    | true =>
      simp only [d47277, d320508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47278 q = 0) : d320509 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47278, d320509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47278, d320509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47279 q = 0) : d320510 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47279, d320510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47279, d320510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47280 q = 0) : d320511 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47280, d320511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47280, d320511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47281 q = 0) : d320512 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47281, d320512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47281, d320512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47282 q = 0) : d320513 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47282, d320513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47282, d320513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33433 (p : Pattern) (selected : d44914 p = 1) : d322010 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d120 q = 1) : d120 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d126 q = 1) : d126 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d44909 q = 1) : d44909 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
    | true =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44910 q = 1) : d322006 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44910, d322006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44910, d322006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44 q = 1) : d44 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d44911 q = 1) : d322007 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44911, d322007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44911, d322007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44912 q = 1) : d322008 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44912, d322008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44912, d322008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d44913 q = 1) : d322009 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44913, d322009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44913, d322009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44914 q = 1) : d322010 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44914, d322010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44914, d322010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro33434 (p : Pattern) (selected : d44921 p = 1) : d322015 p = 1 := by
  have h0 (q : Pattern) (selected : d120 q = 1) : d120 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d126 q = 1) : d126 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d44909 q = 1) : d44909 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
    | true =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44910 q = 1) : d322006 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44910, d322006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44910, d322006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44 q = 1) : d44 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d44911 q = 1) : d322007 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44911, d322007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44911, d322007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44912 q = 1) : d322008 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44912, d322008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44912, d322008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d44913 q = 1) : d322009 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44913, d322009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44913, d322009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d198 q = 1) : d198 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d202 q = 1) : d202 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d44916 q = 1) : d44916 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d206 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
    | true =>
      simp only [d206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d44917 q = 1) : d322011 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44917, d322011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d44917, d322011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d51 q = 1) : d51 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d44918 q = 1) : d322012 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44918, d322012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d44918, d322012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d44919 q = 1) : d322013 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44919, d322013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44919, d322013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d44920 q = 1) : d322014 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44920, d322014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d44920, d322014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d44921 q = 1) : d322015 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44921, d322015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44921, d322015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro33435 (p : Pattern) (selected : d44928 p = 1) : d322022 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d44916 q = 1) : d44916 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d206 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
    | true =>
      simp only [d206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44917 q = 1) : d322011 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44917, d322011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44917, d322011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d51 q = 1) : d51 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d44918 q = 1) : d322012 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44918, d322012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44918, d322012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44926 q = 1) : d322020 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44926, d322020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44926, d322020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44927 q = 1) : d322021 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44927, d322021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44927, d322021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44928 q = 1) : d322022 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44928, d322022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44928, d322022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33436 (p : Pattern) (selected : d44957 p = 1) : d322032 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d44952 q = 1) : d44952 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d263 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11 q selected
    | true =>
      simp only [d263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44953 q = 1) : d322028 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44953, d322028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44953, d322028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d85 q = 1) : d85 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d44954 q = 1) : d322029 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44954, d322029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44954, d322029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44955 q = 1) : d322030 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44955, d322030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44955, d322030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44956 q = 1) : d322031 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44956, d322031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44956, d322031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44957 q = 1) : d322032 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44957, d322032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44957, d322032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33437 (p : Pattern) (selected : d44963 p = 1) : d322038 p = 1 := by
  have h0 (q : Pattern) (selected : d114 q = 1) : d114 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d44922 q = 1) : d322016 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44922, d322016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33433 q selected
    | true =>
      simp only [d44922, d322016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33434 q selected
  have h2 (q : Pattern) (selected : d214 q = 1) : d214 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d44923 q = 1) : d322017 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44923, d322017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44923, d322017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d44924 q = 1) : d322018 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d44924, d322018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44924, d322018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44925 q = 1) : d322019 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d44925, d322019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44925, d322019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44929 q = 1) : d322023 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44929, d322023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44929, d322023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33435 q selected
  have h8 (q : Pattern) (selected : d44930 q = 1) : d322024 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44930, d322024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44930, d322024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d44931 q = 1) : d322025 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d44931, d322025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44931, d322025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d44932 q = 1) : d322026 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d44932, d322026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44932, d322026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d44933 q = 1) : d322027 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d44933, d322027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44933, d322027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d44958 q = 1) : d322033 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44958, d322033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44958, d322033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33436 q selected
  have h13 (q : Pattern) (selected : d44959 q = 1) : d322034 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44959, d322034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d44959, d322034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d44960 q = 1) : d322035 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d44960, d322035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d44960, d322035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d44961 q = 1) : d322036 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d44961, d322036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d44961, d322036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d44962 q = 1) : d322037 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d44962, d322037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d44962, d322037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d44963 q = 1) : d322038 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d44963, d322038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44963, d322038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro33438 (p : Pattern) (selected : d45035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d158 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d35873 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d35873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d35873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d159 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45032 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d45032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d160 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45033 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d45033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d161 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d45034 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d45034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d162 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d45035 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d45035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro33439 (p : Pattern) (selected : d45041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45036 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33438 q selected
    | true =>
      simp only [d45036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45037 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45038 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45039 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45040 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d167 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d168 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d45041 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d45041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro33440 (p : Pattern) (selected : d45047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45042 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33439 q selected
    | true =>
      simp only [d45042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45043 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d45044 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45045 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d172 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d45046 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d45047 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro33441 (p : Pattern) (selected : d45053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45048 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33440 q selected
    | true =>
      simp only [d45048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2 q selected
  have h2 (q : Pattern) (selected : d45049 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45050 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2 q selected
    | true =>
      simp only [d176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d178 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d45051 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d179 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d45052 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45053 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro33442 (p : Pattern) (selected : d45059 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45054 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33441 q selected
    | true =>
      simp only [d45054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45055 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3 q selected
    | true =>
      simp only [d182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d183 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d45056 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45057 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45058 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d45059 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33443 (p : Pattern) (selected : d45071 p = 1) : d322048 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d44989 q = 1) : d44989 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d44995 q = 1) : d44995 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d45031 q = 1) : d45031 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d45060 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33442 q selected
    | true =>
      simp only [d45060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
  have h5 (q : Pattern) (selected : d45061 q = 1) : d322044 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45061, d322044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45061, d322044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45067 q = 1) : d45067 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d45068 q = 1) : d322045 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45068, d322045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45068, d322045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45069 q = 1) : d322046 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45069, d322046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45069, d322046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d45070 q = 1) : d322047 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45070, d322047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45070, d322047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45071 q = 1) : d322048 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45071, d322048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45071, d322048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro33444 (p : Pattern) (selected : d45083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45054 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33441 q selected
    | true =>
      simp only [d45054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45055 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3 q selected
    | true =>
      simp only [d182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d183 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d45056 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45057 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45058 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d45083 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33445 (p : Pattern) (selected : d45092 p = 1) : d322053 p = 1 := by
  have h0 (q : Pattern) (selected : d44989 q = 1) : d44989 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d44995 q = 1) : d44995 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d45031 q = 1) : d45031 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d45060 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33442 q selected
    | true =>
      simp only [d45060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
  have h4 (q : Pattern) (selected : d45061 q = 1) : d322044 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45061, d322044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45061, d322044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d45067 q = 1) : d45067 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d45068 q = 1) : d322045 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45068, d322045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45068, d322045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d45069 q = 1) : d322046 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45069, d322046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45069, d322046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45070 q = 1) : d322047 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45070, d322047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45070, d322047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d45076 q = 1) : d45076 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d45080 q = 1) : d45080 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d45082 q = 1) : d45082 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d45084 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33444 q selected
    | true =>
      simp only [d45084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
  have h13 (q : Pattern) (selected : d45085 q = 1) : d322049 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45085, d322049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d45085, d322049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d45088 q = 1) : d45088 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d45089 q = 1) : d322050 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45089, d322050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d45089, d322050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d45090 q = 1) : d322051 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45090, d322051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d45090, d322051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d45091 q = 1) : d322052 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45091, d322052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45091, d322052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d45092 q = 1) : d322053 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45092, d322053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d45092, d322053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro33446 (p : Pattern) (selected : d45101 p = 1) : d322060 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45082 q = 1) : d45082 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d45084 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33444 q selected
    | true =>
      simp only [d45084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
  have h3 (q : Pattern) (selected : d45085 q = 1) : d322049 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45085, d322049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45085, d322049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45088 q = 1) : d45088 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d45089 q = 1) : d322050 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45089, d322050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45089, d322050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45099 q = 1) : d322058 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45099, d322058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45099, d322058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d45100 q = 1) : d322059 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45100, d322059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45100, d322059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45101 q = 1) : d322060 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45101, d322060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45101, d322060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33447 (p : Pattern) (selected : d45136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45131 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33439 q selected
  have h2 (q : Pattern) (selected : d45042 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33439 q selected
    | true =>
      simp only [d45042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d45132 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45043 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45133 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45134 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
  have h8 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d247 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d248 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d45135 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d249 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d45136 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d45136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro33448 (p : Pattern) (selected : d45142 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45137 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33447 q selected
    | true =>
      simp only [d45137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9 q selected
  have h2 (q : Pattern) (selected : d45138 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45139 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d251 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9 q selected
    | true =>
      simp only [d251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d252 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d45140 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d45141 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45142 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro33449 (p : Pattern) (selected : d45148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45143 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33448 q selected
    | true =>
      simp only [d45143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45144 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10 q selected
    | true =>
      simp only [d257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d45145 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45146 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45147 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d45148 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33450 (p : Pattern) (selected : d45160 p = 1) : d322070 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45130 q = 1) : d45130 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d45149 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33449 q selected
    | true =>
      simp only [d45149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11 q selected
  have h3 (q : Pattern) (selected : d45150 q = 1) : d322066 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45150, d322066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45150, d322066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45156 q = 1) : d45156 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d45157 q = 1) : d322067 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45157, d322067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45157, d322067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45158 q = 1) : d322068 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45158, d322068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45158, d322068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d45159 q = 1) : d322069 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45159, d322069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45159, d322069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45160 q = 1) : d322070 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45160, d322070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45160, d322070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33451 (p : Pattern) (selected : d45166 p = 1) : d322076 p = 1 := by
  have h0 (q : Pattern) (selected : d44983 q = 1) : d44983 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45093 q = 1) : d322054 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45093, d322054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33443 q selected
    | true =>
      simp only [d45093, d322054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33445 q selected
  have h2 (q : Pattern) (selected : d45095 q = 1) : d45095 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d45096 q = 1) : d322055 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45096, d322055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45096, d322055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d45097 q = 1) : d322056 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d45097, d322056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45097, d322056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45098 q = 1) : d322057 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d45098, d322057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45098, d322057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d45102 q = 1) : d322061 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45102, d322061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45102, d322061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33446 q selected
  have h8 (q : Pattern) (selected : d407 q = 1) : d407 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d45103 q = 1) : d322062 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45103, d322062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45103, d322062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45104 q = 1) : d322063 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d45104, d322063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45104, d322063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d45105 q = 1) : d322064 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d45105, d322064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d45105, d322064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d45106 q = 1) : d322065 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d45106, d322065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45106, d322065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d45161 q = 1) : d322071 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45161, d322071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45161, d322071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33450 q selected
  have h14 (q : Pattern) (selected : d463 q = 1) : d463 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d45162 q = 1) : d322072 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45162, d322072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d45162, d322072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d45163 q = 1) : d322073 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d45163, d322073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d45163, d322073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d45164 q = 1) : d322074 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d45164, d322074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d45164, d322074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d45165 q = 1) : d322075 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d45165, d322075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d45165, d322075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d45166 q = 1) : d322076 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d45166, d322076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d45166, d322076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro33452 (p : Pattern) (selected : d45172 p = 1) : d322082 p = 1 := by
  have h0 (q : Pattern) (selected : d99 q = 1) : d99 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d44964 q = 1) : d322039 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d44964, d322039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44964, d322039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33437 q selected
  have h3 (q : Pattern) (selected : d44965 q = 1) : d322040 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d44965, d322040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44965, d322040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44966 q = 1) : d322041 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d44966, d322041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44966, d322041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44967 q = 1) : d322042 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d44967, d322042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44967, d322042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44968 q = 1) : d322043 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d44968, d322043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44968, d322043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d45167 q = 1) : d322077 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d45167, d322077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45167, d322077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33451 q selected
  have h8 (q : Pattern) (selected : d45168 q = 1) : d322078 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d45168, d322078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45168, d322078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d45169 q = 1) : d322079 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d45169, d322079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45169, d322079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45170 q = 1) : d322080 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d45170, d322080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45170, d322080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d45171 q = 1) : d322081 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d45171, d322081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45171, d322081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d45172 q = 1) : d322082 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d45172, d322082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45172, d322082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro33453 (p : Pattern) (selected : d45279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d158 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d159 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1233 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d45277 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d45277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d35873 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d35873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d35873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h7 (q : Pattern) (selected : d45032 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d45032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h8 (q : Pattern) (selected : d160 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d45033 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d45033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45278 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d45278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d161 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d45034 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d45034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d45279 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d45279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d45279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro33454 (p : Pattern) (selected : d45285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45280 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33453 q selected
    | true =>
      simp only [d45280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45281 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d45036 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33438 q selected
    | true =>
      simp only [d45036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d45037 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45282 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d45038 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d45283 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45284 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d166 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d45039 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d45039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d45040 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d45040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d45285 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d45285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro33455 (p : Pattern) (selected : d45293 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45036 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33438 q selected
    | true =>
      simp only [d45036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45037 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45038 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45291 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45292 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d166 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d167 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d168 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d45293 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro33456 (p : Pattern) (selected : d45299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45286 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33454 q selected
    | true =>
      simp only [d45286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45287 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d45288 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45289 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45042 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33439 q selected
    | true =>
      simp only [d45042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d45043 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45044 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45045 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d45290 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45294 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33455 q selected
    | true =>
      simp only [d45294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d45295 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d45295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d45296 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d45297 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d45297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d172 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d173 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d45298 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d45298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d45299 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro33457 (p : Pattern) (selected : d45306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33456 q selected
    | true =>
      simp only [d45300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33440 q selected
  have h2 (q : Pattern) (selected : d45301 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45302 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45048 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33440 q selected
    | true =>
      simp only [d45048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2 q selected
  have h5 (q : Pattern) (selected : d45049 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45050 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d45303 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45304 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d45305 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45306 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro33458 (p : Pattern) (selected : d45310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45048 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33440 q selected
    | true =>
      simp only [d45048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2 q selected
  have h2 (q : Pattern) (selected : d45049 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45050 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45304 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45309 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d45310 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33459 (p : Pattern) (selected : d45316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45307 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33457 q selected
    | true =>
      simp only [d45307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45308 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45311 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33458 q selected
    | true =>
      simp only [d45311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d45312 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d45313 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45314 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45315 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d45316 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33460 (p : Pattern) (selected : d45320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45311 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33458 q selected
    | true =>
      simp only [d45311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45312 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45317 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d45318 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45319 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d45320 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33461 (p : Pattern) (selected : d45332 p = 1) : d322087 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45216 q = 1) : d45216 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d45225 q = 1) : d45225 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d45276 q = 1) : d45276 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d45321 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33459 q selected
    | true =>
      simp only [d45321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33460 q selected
  have h5 (q : Pattern) (selected : d45322 q = 1) : d322083 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45322, d322083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45322, d322083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45328 q = 1) : d45328 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d45329 q = 1) : d322084 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45329, d322084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45329, d322084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45330 q = 1) : d322085 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45330, d322085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45330, d322085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d45331 q = 1) : d322086 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45331, d322086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45331, d322086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45332 q = 1) : d322087 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45332, d322087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45332, d322087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro33462 (p : Pattern) (selected : d45346 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45307 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33457 q selected
    | true =>
      simp only [d45307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45308 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45311 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33458 q selected
    | true =>
      simp only [d45311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d45312 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d45313 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45314 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45315 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d45346 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33463 (p : Pattern) (selected : d45347 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45311 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33458 q selected
    | true =>
      simp only [d45311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45312 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45317 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d45318 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45319 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d45347 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33464 (p : Pattern) (selected : d45356 p = 1) : d322092 p = 1 := by
  have h0 (q : Pattern) (selected : d45216 q = 1) : d45216 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45225 q = 1) : d45225 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d45276 q = 1) : d45276 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d45321 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33459 q selected
    | true =>
      simp only [d45321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33460 q selected
  have h4 (q : Pattern) (selected : d45322 q = 1) : d322083 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45322, d322083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45322, d322083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d45328 q = 1) : d45328 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d45329 q = 1) : d322084 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45329, d322084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45329, d322084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d45330 q = 1) : d322085 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45330, d322085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45330, d322085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45331 q = 1) : d322086 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45331, d322086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45331, d322086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d45338 q = 1) : d45338 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d45343 q = 1) : d45343 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d45345 q = 1) : d45345 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d45348 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33462 q selected
    | true =>
      simp only [d45348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33463 q selected
  have h13 (q : Pattern) (selected : d45349 q = 1) : d322088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45349, d322088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d45349, d322088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d45352 q = 1) : d45352 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d45353 q = 1) : d322089 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45353, d322089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d45353, d322089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d45354 q = 1) : d322090 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45354, d322090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d45354, d322090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d45355 q = 1) : d322091 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45355, d322091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45355, d322091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d45356 q = 1) : d322092 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45356, d322092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d45356, d322092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro33465 (p : Pattern) (selected : d45376 p = 1) : d322099 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45345 q = 1) : d45345 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d45348 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33462 q selected
    | true =>
      simp only [d45348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33463 q selected
  have h3 (q : Pattern) (selected : d45349 q = 1) : d322088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45349, d322088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45349, d322088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45352 q = 1) : d45352 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d45353 q = 1) : d322089 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45353, d322089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45353, d322089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45374 q = 1) : d322097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45374, d322097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45374, d322097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d45375 q = 1) : d322098 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45375, d322098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45375, d322098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45376 q = 1) : d322099 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45376, d322099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45376, d322099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33466 (p : Pattern) (selected : d45439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45429 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33454 q selected
  have h2 (q : Pattern) (selected : d45286 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33454 q selected
    | true =>
      simp only [d45286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d45430 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45287 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45431 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45432 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45131 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33439 q selected
  have h8 (q : Pattern) (selected : d45042 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33439 q selected
    | true =>
      simp only [d45042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d45132 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45043 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d45043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d45133 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d45134 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d45134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d45433 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d45434 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33455 q selected
  have h15 (q : Pattern) (selected : d45294 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33455 q selected
    | true =>
      simp only [d45294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d45435 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d45435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d45295 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d45295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d45436 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d45436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d45437 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d45437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
  have h21 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d247 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d248 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d45438 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d45438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d45439 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d45439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro33467 (p : Pattern) (selected : d45446 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45440 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33466 q selected
    | true =>
      simp only [d45440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33447 q selected
  have h2 (q : Pattern) (selected : d45441 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45442 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45137 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33447 q selected
    | true =>
      simp only [d45137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9 q selected
  have h5 (q : Pattern) (selected : d45138 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45139 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d45443 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45444 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d45445 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45446 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro33468 (p : Pattern) (selected : d45450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45137 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33447 q selected
    | true =>
      simp only [d45137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9 q selected
  have h2 (q : Pattern) (selected : d45138 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45139 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45444 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45449 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d45450 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33469 (p : Pattern) (selected : d45456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33467 q selected
    | true =>
      simp only [d45447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33468 q selected
    | true =>
      simp only [d45451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d45452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d45453 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45454 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45455 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d45456 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33470 (p : Pattern) (selected : d45460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33468 q selected
    | true =>
      simp only [d45451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45457 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d45458 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45459 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d45460 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33471 (p : Pattern) (selected : d45472 p = 1) : d322109 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45428 q = 1) : d45428 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d45461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33469 q selected
    | true =>
      simp only [d45461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33470 q selected
  have h3 (q : Pattern) (selected : d45462 q = 1) : d322105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45462, d322105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45462, d322105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45468 q = 1) : d45468 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d45469 q = 1) : d322106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45469, d322106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45469, d322106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45470 q = 1) : d322107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45470, d322107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45470, d322107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d45471 q = 1) : d322108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45471, d322108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45471, d322108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45472 q = 1) : d322109 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45472, d322109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45472, d322109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33472 (p : Pattern) (selected : d45489 p = 1) : d322115 p = 1 := by
  have h0 (q : Pattern) (selected : d45208 q = 1) : d45208 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45357 q = 1) : d322093 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45357, d322093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33461 q selected
    | true =>
      simp only [d45357, d322093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33464 q selected
  have h2 (q : Pattern) (selected : d45370 q = 1) : d45370 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d45371 q = 1) : d322094 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45371, d322094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45371, d322094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d45372 q = 1) : d322095 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d45372, d322095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45372, d322095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45373 q = 1) : d322096 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d45373, d322096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45373, d322096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d45377 q = 1) : d322100 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45377, d322100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45377, d322100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33465 q selected
  have h8 (q : Pattern) (selected : d45379 q = 1) : d45379 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d45380 q = 1) : d322101 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45380, d322101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45380, d322101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45381 q = 1) : d322102 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d45381, d322102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45381, d322102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d45382 q = 1) : d322103 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d45382, d322103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d45382, d322103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d45383 q = 1) : d322104 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d45383, d322104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45383, d322104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d45473 q = 1) : d322110 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45473, d322110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45473, d322110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33471 q selected
  have h14 (q : Pattern) (selected : d45484 q = 1) : d45484 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d45485 q = 1) : d322111 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45485, d322111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d45485, d322111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d45486 q = 1) : d322112 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d45486, d322112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d45486, d322112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d45487 q = 1) : d322113 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d45487, d322113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d45487, d322113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d45488 q = 1) : d322114 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d45488, d322114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d45488, d322114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d45489 q = 1) : d322115 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d45489, d322115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d45489, d322115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro33473 (p : Pattern) (selected : d45495 p = 1) : d322121 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45490 q = 1) : d322116 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d45490, d322116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45490, d322116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33472 q selected
  have h2 (q : Pattern) (selected : d45491 q = 1) : d322117 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d45491, d322117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45491, d322117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45492 q = 1) : d322118 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d45492, d322118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45492, d322118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45493 q = 1) : d322119 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d45493, d322119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45493, d322119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d45494 q = 1) : d322120 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d45494, d322120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45494, d322120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45495 q = 1) : d322121 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d45495, d322121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45495, d322121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33474 (p : Pattern) (selected : d45630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d158 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d35873 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d35873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d35873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d159 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45032 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d45032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d160 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45033 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d45033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45629 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d45629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d45630 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d45630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro33475 (p : Pattern) (selected : d45637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d158 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d159 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1233 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d45277 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d45277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d35873 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d35873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d35873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h7 (q : Pattern) (selected : d45032 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d45032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h8 (q : Pattern) (selected : d45634 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d45634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d45635 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d45635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d160 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d161 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d45636 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d45636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d45636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d45637 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d45637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro33476 (p : Pattern) (selected : d45643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45631 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33474 q selected
    | true =>
      simp only [d45631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45632 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d45280 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33453 q selected
    | true =>
      simp only [d45280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d45281 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45633 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45638 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33475 q selected
    | true =>
      simp only [d45638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45639 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d45036 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33438 q selected
    | true =>
      simp only [d45036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d45037 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d45037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d45640 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d45641 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d45642 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d45642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d45282 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h14 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d45038 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d45283 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d45283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d45284 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d45284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d45643 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d45643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro33477 (p : Pattern) (selected : d45648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45280 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33453 q selected
    | true =>
      simp only [d45280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45281 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d45036 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33438 q selected
    | true =>
      simp only [d45036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d45037 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45282 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d45038 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d45283 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45284 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d45291 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d45291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d45292 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d45292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d45648 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d45648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro33478 (p : Pattern) (selected : d45656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45280 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33453 q selected
    | true =>
      simp only [d45280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45281 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d45036 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33438 q selected
    | true =>
      simp only [d45036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d45037 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45282 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45654 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45655 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d45038 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d45291 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d45291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d45292 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d45292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d45656 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro33479 (p : Pattern) (selected : d45661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45036 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33438 q selected
    | true =>
      simp only [d45036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45037 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45038 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45039 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45040 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d45661 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d45661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro33480 (p : Pattern) (selected : d45667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45644 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33476 q selected
    | true =>
      simp only [d45644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45645 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d45646 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45647 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45649 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33477 q selected
    | true =>
      simp only [d45649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d45650 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45651 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45652 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d45653 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45657 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33478 q selected
    | true =>
      simp only [d45657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d45658 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d45658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d45659 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d45660 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d45660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d45662 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33479 q selected
    | true =>
      simp only [d45662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d45663 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d45663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d45664 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d45665 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d45665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d45666 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d45666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d45667 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro33481 (p : Pattern) (selected : d45670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45286 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33454 q selected
    | true =>
      simp only [d45286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45287 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d45288 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45289 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45662 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33479 q selected
    | true =>
      simp only [d45662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d45663 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45664 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45665 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d45668 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45669 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d45669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d45670 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro33482 (p : Pattern) (selected : d45674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45662 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33479 q selected
    | true =>
      simp only [d45662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45663 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d45664 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45665 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45669 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d45674 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33483 (p : Pattern) (selected : d45681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45671 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33480 q selected
    | true =>
      simp only [d45671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33481 q selected
  have h2 (q : Pattern) (selected : d45672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45673 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45675 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33481 q selected
    | true =>
      simp only [d45675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33482 q selected
  have h5 (q : Pattern) (selected : d45676 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45677 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d45678 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45679 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d45680 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45681 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro33484 (p : Pattern) (selected : d45685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45675 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33481 q selected
    | true =>
      simp only [d45675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33482 q selected
  have h2 (q : Pattern) (selected : d45676 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45677 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45679 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45684 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d45685 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33485 (p : Pattern) (selected : d45691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45682 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33483 q selected
    | true =>
      simp only [d45682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45683 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45686 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33484 q selected
    | true =>
      simp only [d45686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d45687 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d45688 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45689 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45690 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d45691 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33486 (p : Pattern) (selected : d45695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45686 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33484 q selected
    | true =>
      simp only [d45686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45687 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45692 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d45693 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45694 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d45695 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro33487 (p : Pattern) (selected : d45707 p = 1) : d322127 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45558 q = 1) : d45558 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d45567 q = 1) : d45567 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d45628 q = 1) : d45628 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d45696 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33485 q selected
    | true =>
      simp only [d45696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33486 q selected
  have h5 (q : Pattern) (selected : d45697 q = 1) : d322123 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45697, d322123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45697, d322123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45703 q = 1) : d45703 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d45704 q = 1) : d322124 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45704, d322124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45704, d322124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45705 q = 1) : d322125 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45705, d322125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45705, d322125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d45706 q = 1) : d322126 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45706, d322126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45706, d322126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45707 q = 1) : d322127 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45707, d322127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45707, d322127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro33488 (p : Pattern) (selected : d45721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45682 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33483 q selected
    | true =>
      simp only [d45682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45683 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45686 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33484 q selected
    | true =>
      simp only [d45686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d45687 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d45688 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45689 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45690 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d45721 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33489 (p : Pattern) (selected : d45722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45686 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33484 q selected
    | true =>
      simp only [d45686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45687 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45692 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d45693 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45694 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d45722 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33490 (p : Pattern) (selected : d45731 p = 1) : d322132 p = 1 := by
  have h0 (q : Pattern) (selected : d45558 q = 1) : d45558 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45567 q = 1) : d45567 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d45628 q = 1) : d45628 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d45696 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33485 q selected
    | true =>
      simp only [d45696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33486 q selected
  have h4 (q : Pattern) (selected : d45697 q = 1) : d322123 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45697, d322123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45697, d322123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d45703 q = 1) : d45703 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d45704 q = 1) : d322124 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45704, d322124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45704, d322124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d45705 q = 1) : d322125 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45705, d322125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45705, d322125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45706 q = 1) : d322126 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45706, d322126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45706, d322126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d45713 q = 1) : d45713 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d45718 q = 1) : d45718 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d45720 q = 1) : d45720 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d45723 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33488 q selected
    | true =>
      simp only [d45723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33489 q selected
  have h13 (q : Pattern) (selected : d45724 q = 1) : d322128 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45724, d322128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d45724, d322128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d45727 q = 1) : d45727 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d45728 q = 1) : d322129 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45728, d322129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d45728, d322129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d45729 q = 1) : d322130 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45729, d322130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d45729, d322130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d45730 q = 1) : d322131 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45730, d322131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45730, d322131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d45731 q = 1) : d322132 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45731, d322132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d45731, d322132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro33491 (p : Pattern) (selected : d45751 p = 1) : d322139 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45720 q = 1) : d45720 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d45723 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33488 q selected
    | true =>
      simp only [d45723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33489 q selected
  have h3 (q : Pattern) (selected : d45724 q = 1) : d322128 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45724, d322128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45724, d322128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45727 q = 1) : d45727 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d45728 q = 1) : d322129 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45728, d322129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45728, d322129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45749 q = 1) : d322137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45749, d322137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45749, d322137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d45750 q = 1) : d322138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45750, d322138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45750, d322138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45751 q = 1) : d322139 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45751, d322139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45751, d322139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro33492 (p : Pattern) (selected : d45839 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45821 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33476 q selected
  have h2 (q : Pattern) (selected : d45644 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33476 q selected
    | true =>
      simp only [d45644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d45822 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45645 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45823 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45824 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45825 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33477 q selected
  have h8 (q : Pattern) (selected : d45649 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33477 q selected
    | true =>
      simp only [d45649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d45826 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45650 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d45650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d45827 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d45828 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d45828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d45829 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d45830 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33478 q selected
  have h15 (q : Pattern) (selected : d45657 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33478 q selected
    | true =>
      simp only [d45657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d45831 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d45831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d45658 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d45658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d45832 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d45832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d45833 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d45833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d45834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33479 q selected
  have h21 (q : Pattern) (selected : d45662 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33479 q selected
    | true =>
      simp only [d45662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d45835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d45835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d45663 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d45663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d45836 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d45836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d45837 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d45837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d45838 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d45838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d45839 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d45839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro33493 (p : Pattern) (selected : d45842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45429 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33454 q selected
  have h2 (q : Pattern) (selected : d45286 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33454 q selected
    | true =>
      simp only [d45286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d45430 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45287 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45431 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45432 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33479 q selected
  have h8 (q : Pattern) (selected : d45662 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33479 q selected
    | true =>
      simp only [d45662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d45835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45663 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d45663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d45836 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d45837 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d45837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d45840 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d45841 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d45841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d45842 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d45842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro33494 (p : Pattern) (selected : d45846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33479 q selected
  have h2 (q : Pattern) (selected : d45662 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33479 q selected
    | true =>
      simp only [d45662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d45835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45663 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45836 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45837 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45841 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d45846 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33495 (p : Pattern) (selected : d45853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45843 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33492 q selected
    | true =>
      simp only [d45843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33493 q selected
  have h2 (q : Pattern) (selected : d45844 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45845 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45847 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33493 q selected
    | true =>
      simp only [d45847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33494 q selected
  have h5 (q : Pattern) (selected : d45848 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45849 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d45850 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45851 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d45852 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d45853 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d45853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro33496 (p : Pattern) (selected : d45857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45847 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33493 q selected
    | true =>
      simp only [d45847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33494 q selected
  have h2 (q : Pattern) (selected : d45848 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45849 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45851 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45856 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d45857 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33497 (p : Pattern) (selected : d45863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45854 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33495 q selected
    | true =>
      simp only [d45854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45858 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33496 q selected
    | true =>
      simp only [d45858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d45859 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d45860 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45861 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d45862 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d45862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d45863 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d45863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro33498 (p : Pattern) (selected : d45867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45858 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33496 q selected
    | true =>
      simp only [d45858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d45859 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d45864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d45865 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d45866 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d45866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d45867 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d45867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro33499 (p : Pattern) (selected : d45879 p = 1) : d322149 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d45820 q = 1) : d45820 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d45868 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33497 q selected
    | true =>
      simp only [d45868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33498 q selected
  have h3 (q : Pattern) (selected : d45869 q = 1) : d322145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45869, d322145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45869, d322145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d45875 q = 1) : d45875 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d45876 q = 1) : d322146 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45876, d322146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d45876, d322146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d45877 q = 1) : d322147 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45877, d322147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45877, d322147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d45878 q = 1) : d322148 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45878, d322148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45878, d322148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d45879 q = 1) : d322149 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45879, d322149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45879, d322149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
end NetHack.Soko22Hazard87
