import NetHack.Soko22Hazard87.AndIntroBlocks0222
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro55750 (p : Pattern) (ha : d20643 p = 1) (hb : d180908 p = 1) : d181265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20631 q = 1) (hb : d180908 q = 1) : d181246 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20631, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55748 q ha hb
    | true =>
      simp only [d20631, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20632 q = 1) (hb : d180908 q = 1) : d181247 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20632, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20632, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20638 q = 1) (hb : d180908 q = 1) : d181260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20638, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55736 q ha hb
    | true =>
      simp only [d20638, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20639 q = 1) (hb : d180908 q = 1) : d181261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20639, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20639, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20640 q = 1) (hb : d180908 q = 1) : d181262 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20640, d181262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20640, d181262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20641 q = 1) (hb : d180908 q = 1) : d181263 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20641, d181263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20641, d181263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20642 q = 1) (hb : d180908 q = 1) : d181264 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20642, d181264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20642, d181264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20643 q = 1) (hb : d180908 q = 1) : d181265 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20643, d181265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20643, d181265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55751 (p : Pattern) (ha : d9987 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1121 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9829 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9829, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9829, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1122 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9830 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9830, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9830, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9831 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9868 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d9987 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro55752 (p : Pattern) (ha : d13190 p = 1) (hb : d180908 p = 1) : d181268 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1391 q = 1) : d1391 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1121 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1392 q = 1) (hb : d131097 q = 1) : d19034 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d131097, d19034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1392, d131097, d19034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1122 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1393 q = 1) (hb : d180908 q = 1) : d181221 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d180908, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1393, d180908, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1394 q = 1) (hb : d180908 q = 1) : d181222 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1394, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1400 q = 1) (hb : d180908 q = 1) : d181252 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1400, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d13190 q = 1) (hb : d180908 q = 1) : d181268 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13190, d181268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13190, d181268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro55753 (p : Pattern) (ha : d20661 p = 1) (hb : d180908 p = 1) : d181274 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d180908 q = 1) : d181225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55745 q ha hb
    | true =>
      simp only [d16673, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55735 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d180908 q = 1) : d181226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d180908 q = 1) : d181227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d180908 q = 1) : d181235 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55735 q ha hb
    | true =>
      simp only [d16676, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55743 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d180908 q = 1) : d181236 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d180908 q = 1) : d181237 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d180908 q = 1) : d181238 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16743 q = 1) (hb : d180908 q = 1) : d181269 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16743, d181269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55735 q ha hb
    | true =>
      simp only [d16743, d181269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55752 q ha hb
  have h9 (q : Pattern) (ha : d16744 q = 1) (hb : d180908 q = 1) : d181270 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16744, d181270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16744, d181270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16745 q = 1) (hb : d180908 q = 1) : d181271 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16745, d181271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16745, d181271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16746 q = 1) (hb : d180908 q = 1) : d181272 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16746, d181272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16746, d181272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16747 q = 1) (hb : d180908 q = 1) : d181273 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16747, d181273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16747, d181273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9834 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55740 q ha hb
    | true =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55732 q ha hb
  have h14 (q : Pattern) (ha : d9835 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9836 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9851 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55732 q ha hb
    | true =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55742 q ha hb
  have h17 (q : Pattern) (ha : d9852 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9853 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9854 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9988 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55732 q ha hb
    | true =>
      simp only [d9988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55751 q ha hb
  have h21 (q : Pattern) (ha : d9989 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d9990 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9991 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d9992 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d20661 q = 1) (hb : d180908 q = 1) : d181274 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20661, d181274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d20661, d181274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro55754 (p : Pattern) (ha : d20667 p = 1) (hb : d180908 p = 1) : d181280 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20662 q = 1) (hb : d180908 q = 1) : d181275 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20662, d181275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55753 q ha hb
    | true =>
      simp only [d20662, d181275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20663 q = 1) (hb : d180908 q = 1) : d181276 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20663, d181276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20663, d181276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20664 q = 1) (hb : d180908 q = 1) : d181277 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20664, d181277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20664, d181277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20665 q = 1) (hb : d180908 q = 1) : d181278 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20665, d181278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20665, d181278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20666 q = 1) (hb : d180908 q = 1) : d181279 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20666, d181279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20666, d181279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20667 q = 1) (hb : d180908 q = 1) : d181280 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20667, d181280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20667, d181280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55755 (p : Pattern) (ha : d130994 p = 1) (hb : d180908 p = 1) : d181286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20644 q = 1) (hb : d180908 q = 1) : d181266 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20644, d181266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55749 q ha hb
    | true =>
      simp only [d20644, d181266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55750 q ha hb
  have h2 (q : Pattern) (ha : d130990 q = 1) (hb : d180908 q = 1) : d181267 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130990, d181267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130990, d181267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20668 q = 1) (hb : d180908 q = 1) : d181281 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20668, d181281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55754 q ha hb
    | true =>
      simp only [d20668, d181281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20669 q = 1) (hb : d180908 q = 1) : d181282 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20669, d181282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20669, d181282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130991 q = 1) (hb : d180908 q = 1) : d181283 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130991, d181283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130991, d181283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130992 q = 1) (hb : d180908 q = 1) : d181284 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130992, d181284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130992, d181284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130993 q = 1) (hb : d180908 q = 1) : d181285 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130993, d181285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130993, d181285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130994 q = 1) (hb : d180908 q = 1) : d181286 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130994, d181286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130994, d181286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55756 (p : Pattern) (ha : d131000 p = 1) (hb : d180908 p = 1) : d181303 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130995 q = 1) (hb : d180908 q = 1) : d181287 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130995, d181287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130995, d181287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55755 q ha hb
  have h2 (q : Pattern) (ha : d20685 q = 1) (hb : d180908 q = 1) : d181298 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20685, d181298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20685, d181298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55738 q ha hb
  have h3 (q : Pattern) (ha : d130996 q = 1) (hb : d180908 q = 1) : d181299 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130996, d181299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130996, d181299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130997 q = 1) (hb : d180908 q = 1) : d181300 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130997, d181300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130997, d181300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130998 q = 1) (hb : d180908 q = 1) : d181301 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130998, d181301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130998, d181301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130999 q = 1) (hb : d180908 q = 1) : d181302 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130999, d181302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130999, d181302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d131000 q = 1) (hb : d180908 q = 1) : d181303 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131000, d181303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131000, d181303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro55757 (p : Pattern) (ha : d131006 p = 1) (hb : d180908 p = 1) : d181309 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131001 q = 1) (hb : d180908 q = 1) : d181304 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131001, d181304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131001, d181304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55756 q ha hb
  have h2 (q : Pattern) (ha : d131002 q = 1) (hb : d180908 q = 1) : d181305 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131002, d181305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131002, d181305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131003 q = 1) (hb : d180908 q = 1) : d181306 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131003, d181306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131003, d181306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131004 q = 1) (hb : d180908 q = 1) : d181307 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131004, d181307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131004, d181307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131005 q = 1) (hb : d180908 q = 1) : d181308 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131005, d181308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131005, d181308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131006 q = 1) (hb : d180908 q = 1) : d181309 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131006, d181309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131006, d181309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55758 (p : Pattern) (ha : d10121 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1570 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10111 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10111, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10111, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1571 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10112 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10112, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10112, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10113 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d10115 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10116 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10116, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10116, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10117 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10118 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10118, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10118, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10119 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d10120 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d10085 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10086 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10086, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10086, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d10087 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10088 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10088, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10088, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d10089 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d10105 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h19 (q : Pattern) (ha : d10121 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro55759 (p : Pattern) (ha : d10163 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10159 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10159, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10159, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1583 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10160 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10160, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10160, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10161 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10162 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10135 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10136 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10136, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10136, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10137 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10138 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10138, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10138, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d10139 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d10140 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d10163 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro55760 (p : Pattern) (ha : d15435 p = 1) (hb : d180908 p = 1) : d181381 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1868 q = 1) : d1868 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1869 q = 1) (hb : d131097 q = 1) : d19313 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d131097, d19313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1869, d131097, d19313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1583 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1870 q = 1) (hb : d180908 q = 1) : d181378 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d180908, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1870, d180908, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1871 q = 1) (hb : d180908 q = 1) : d181379 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1871, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1877 q = 1) (hb : d180908 q = 1) : d181380 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1877, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d15412 q = 1) : d15412 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10135 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15413 q = 1) (hb : d131097 q = 1) : d19278 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d131097, d19278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d15413, d131097, d19278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d10137 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d15414 q = 1) (hb : d180908 q = 1) : d181357 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, d180908, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15414, d180908, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d15415 q = 1) (hb : d180908 q = 1) : d181358 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15415, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d15416 q = 1) (hb : d180908 q = 1) : d181359 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15416, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d15435 q = 1) (hb : d180908 q = 1) : d181381 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15435, d181381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15435, d181381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro55761 (p : Pattern) (ha : d17032 p = 1) (hb : d180908 p = 1) : d181350 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1862 q = 1) : d1862 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1570 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1863 q = 1) (hb : d131097 q = 1) : d19263 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d131097, d19263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1863, d131097, d19263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1571 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1864 q = 1) (hb : d180908 q = 1) : d181345 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d180908, d181345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1864, d180908, d181345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1865 q = 1) (hb : d180908 q = 1) : d181346 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d181346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1865, d181346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d17027 q = 1) : d17027 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10115 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17028 q = 1) (hb : d131097 q = 1) : d19266 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17028, d131097, d19266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d17028, d131097, d19266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10117 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d17029 q = 1) (hb : d180908 q = 1) : d181347 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17029, d180908, d181347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17029, d180908, d181347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d17030 q = 1) (hb : d180908 q = 1) : d181348 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17030, d181348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17030, d181348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d17031 q = 1) (hb : d180908 q = 1) : d181349 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17031, d181349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17031, d181349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1 q = 1) (hb : d15397 q = 1) : d15397 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d10085 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d15398 q = 1) (hb : d131097 q = 1) : d19245 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d131097, d19245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d15398, d131097, d19245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d10087 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d15399 q = 1) (hb : d180908 q = 1) : d181329 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d180908, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15399, d180908, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d15400 q = 1) (hb : d180908 q = 1) : d181330 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d15400, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h20 (q : Pattern) (ha : d15401 q = 1) (hb : d180908 q = 1) : d181339 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15401, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d15401, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h21 (q : Pattern) (ha : d17032 q = 1) (hb : d180908 q = 1) : d181350 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17032, d181350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17032, d181350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro55762 (p : Pattern) (ha : d20710 p = 1) (hb : d180908 p = 1) : d181387 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17053 q = 1) (hb : d180908 q = 1) : d181382 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55761 q ha hb
    | true =>
      simp only [d17053, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55760 q ha hb
  have h2 (q : Pattern) (ha : d17054 q = 1) (hb : d180908 q = 1) : d181383 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17054, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17055 q = 1) (hb : d180908 q = 1) : d181384 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17056 q = 1) (hb : d180908 q = 1) : d181385 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17056, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17057 q = 1) (hb : d180908 q = 1) : d181386 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17057, d181386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17057, d181386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10164 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55758 q ha hb
    | true =>
      simp only [d10164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55759 q ha hb
  have h7 (q : Pattern) (ha : d10165 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10166 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10167 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10168 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20710 q = 1) (hb : d180908 q = 1) : d181387 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20710, d181387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20710, d181387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro55763 (p : Pattern) (ha : d20751 p = 1) (hb : d180908 p = 1) : d181419 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20711 q = 1) (hb : d180908 q = 1) : d181388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20711, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55762 q ha hb
    | true =>
      simp only [d20711, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20712 q = 1) (hb : d180908 q = 1) : d181389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20712, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20712, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20748 q = 1) (hb : d180908 q = 1) : d181416 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20748, d181416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20748, d181416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20749 q = 1) (hb : d180908 q = 1) : d181417 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20749, d181417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20749, d181417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20750 q = 1) (hb : d180908 q = 1) : d181418 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20750, d181418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20750, d181418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20751 q = 1) (hb : d180908 q = 1) : d181419 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20751, d181419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20751, d181419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55764 (p : Pattern) (ha : d20757 p = 1) (hb : d180908 p = 1) : d181425 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20752 q = 1) (hb : d180908 q = 1) : d181420 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20752, d181420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55763 q ha hb
    | true =>
      simp only [d20752, d181420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20753 q = 1) (hb : d180908 q = 1) : d181421 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20753, d181421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20753, d181421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20754 q = 1) (hb : d180908 q = 1) : d181422 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20754, d181422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20754, d181422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20755 q = 1) (hb : d180908 q = 1) : d181423 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20755, d181423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20755, d181423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20756 q = 1) (hb : d180908 q = 1) : d181424 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20756, d181424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20756, d181424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20757 q = 1) (hb : d180908 q = 1) : d181425 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20757, d181425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20757, d181425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55765 (p : Pattern) (ha : d10069 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1665 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10032 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10032, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10032, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1666 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10033 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10033, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10033, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10034 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d10036 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10037 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10037, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10037, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10038 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10039 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10039, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10039, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10040 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d10041 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d10046 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10047 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10047, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10047, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d10048 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10049 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10049, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10049, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d10050 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d10063 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d10064 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10064, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10064, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d10065 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d10066 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10066, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10066, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  have h22 (q : Pattern) (ha : d10067 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d10067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d10068 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d10069 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro55766 (p : Pattern) (ha : d10091 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1555 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10070 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10070, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10070, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1556 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10071 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10071, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10071, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10072 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d10074 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10075 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10075, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10075, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10076 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10077 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10077, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10077, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10078 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d10079 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d10063 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10064 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10064, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10064, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d10065 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10066 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10066, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10066, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d10067 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d10085 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d10086 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10086, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10086, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d10087 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d10088 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10088, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10088, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  have h22 (q : Pattern) (ha : d10089 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d10089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d10090 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d10091 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro55767 (p : Pattern) (ha : d10106 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10100 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10100, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10100, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10101 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10102 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10102, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10102, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10103 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d10085 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10086 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10086, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10086, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10087 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10088 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10088, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10088, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10089 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d10104 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10105 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d10106 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro55768 (p : Pattern) (ha : d10141 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5134 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10125 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10125, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10125, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5135 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10126 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10126, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10126, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10127 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10128 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10135 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10136 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10136, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10136, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10137 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10138 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10138, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10138, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d10139 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d10140 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d10141 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro55769 (p : Pattern) (ha : d15417 p = 1) (hb : d180908 p = 1) : d181360 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d6496 q = 1) : d6496 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5134 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6497 q = 1) (hb : d131097 q = 1) : d19274 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6497, d131097, d19274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6497, d131097, d19274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5135 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6498 q = 1) (hb : d180908 q = 1) : d181354 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6498, d180908, d181354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6498, d180908, d181354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6499 q = 1) (hb : d180908 q = 1) : d181355 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6499, d181355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6499, d181355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6500 q = 1) (hb : d180908 q = 1) : d181356 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6500, d181356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6500, d181356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d15412 q = 1) : d15412 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10135 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15413 q = 1) (hb : d131097 q = 1) : d19278 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d131097, d19278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d15413, d131097, d19278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d10137 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d15414 q = 1) (hb : d180908 q = 1) : d181357 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, d180908, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15414, d180908, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d15415 q = 1) (hb : d180908 q = 1) : d181358 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15415, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d15416 q = 1) (hb : d180908 q = 1) : d181359 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15416, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d15417 q = 1) (hb : d180908 q = 1) : d181360 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15417, d181360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15417, d181360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro55770 (p : Pattern) (ha : d17010 p = 1) (hb : d180908 p = 1) : d181323 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1853 q = 1) : d1853 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1665 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1854 q = 1) (hb : d131097 q = 1) : d19223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1854, d131097, d19223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1854, d131097, d19223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1666 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1855 q = 1) (hb : d180908 q = 1) : d181313 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1855, d180908, d181313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1855, d180908, d181313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1856 q = 1) (hb : d180908 q = 1) : d181314 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1856, d181314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1856, d181314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d17004 q = 1) : d17004 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10036 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17005 q = 1) (hb : d131097 q = 1) : d19226 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, d131097, d19226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d17005, d131097, d19226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10038 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d17006 q = 1) (hb : d180908 q = 1) : d181315 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17006, d180908, d181315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17006, d180908, d181315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d17007 q = 1) (hb : d180908 q = 1) : d181316 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17007, d181316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17007, d181316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d17008 q = 1) (hb : d180908 q = 1) : d181317 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17008, d181317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17008, d181317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1 q = 1) (hb : d15380 q = 1) : d15380 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d10046 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d15381 q = 1) (hb : d131097 q = 1) : d19230 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15381, d131097, d19230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d15381, d131097, d19230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d10048 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d15382 q = 1) (hb : d180908 q = 1) : d181318 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15382, d180908, d181318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15382, d180908, d181318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d15383 q = 1) (hb : d180908 q = 1) : d181319 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15383, d181319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d15383, d181319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h20 (q : Pattern) (ha : d1 q = 1) (hb : d15387 q = 1) : d15387 q = 1 := by
    exact hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d10063 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d15388 q = 1) (hb : d131097 q = 1) : d19233 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, d131097, d19233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d15388, d131097, d19233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d10065 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d15389 q = 1) (hb : d180908 q = 1) : d181320 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15389, d180908, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d15389, d180908, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d15390 q = 1) (hb : d180908 q = 1) : d181321 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15390, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d15390, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h26 (q : Pattern) (ha : d17009 q = 1) (hb : d180908 q = 1) : d181322 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17009, d181322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d17009, d181322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d17010 q = 1) (hb : d180908 q = 1) : d181323 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17010, d181323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17010, d181323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro55771 (p : Pattern) (ha : d17017 p = 1) (hb : d180908 p = 1) : d181332 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1857 q = 1) : d1857 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1555 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1858 q = 1) (hb : d131097 q = 1) : d19238 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, d131097, d19238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1858, d131097, d19238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1556 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1859 q = 1) (hb : d180908 q = 1) : d181324 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, d180908, d181324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1859, d180908, d181324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1860 q = 1) (hb : d180908 q = 1) : d181325 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, d181325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1860, d181325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d17011 q = 1) : d17011 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10074 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17012 q = 1) (hb : d131097 q = 1) : d19241 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17012, d131097, d19241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d17012, d131097, d19241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10076 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d17013 q = 1) (hb : d180908 q = 1) : d181326 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17013, d180908, d181326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17013, d180908, d181326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d17014 q = 1) (hb : d180908 q = 1) : d181327 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17014, d181327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17014, d181327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d17015 q = 1) (hb : d180908 q = 1) : d181328 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17015, d181328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17015, d181328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1 q = 1) (hb : d15387 q = 1) : d15387 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d10063 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d15388 q = 1) (hb : d131097 q = 1) : d19233 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, d131097, d19233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d15388, d131097, d19233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d10065 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d15389 q = 1) (hb : d180908 q = 1) : d181320 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15389, d180908, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15389, d180908, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d15390 q = 1) (hb : d180908 q = 1) : d181321 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15390, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d15390, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h20 (q : Pattern) (ha : d1 q = 1) (hb : d15397 q = 1) : d15397 q = 1 := by
    exact hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d10085 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d15398 q = 1) (hb : d131097 q = 1) : d19245 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d131097, d19245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d15398, d131097, d19245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d10087 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d15399 q = 1) (hb : d180908 q = 1) : d181329 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d180908, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d15399, d180908, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d15400 q = 1) (hb : d180908 q = 1) : d181330 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d15400, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h26 (q : Pattern) (ha : d17016 q = 1) (hb : d180908 q = 1) : d181331 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17016, d181331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d17016, d181331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d17017 q = 1) (hb : d180908 q = 1) : d181332 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17017, d181332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17017, d181332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro55772 (p : Pattern) (ha : d17022 p = 1) (hb : d180908 p = 1) : d181340 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d13486 q = 1) : d13486 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13487 q = 1) (hb : d131097 q = 1) : d19253 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13487, d131097, d19253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13487, d131097, d19253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10101 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13488 q = 1) (hb : d180908 q = 1) : d181336 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13488, d180908, d181336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13488, d180908, d181336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13489 q = 1) (hb : d180908 q = 1) : d181337 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13489, d181337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13489, d181337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d15397 q = 1) : d15397 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10085 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15398 q = 1) (hb : d131097 q = 1) : d19245 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d131097, d19245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d15398, d131097, d19245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10087 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15399 q = 1) (hb : d180908 q = 1) : d181329 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d180908, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15399, d180908, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d15400 q = 1) (hb : d180908 q = 1) : d181330 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15400, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d17021 q = 1) (hb : d180908 q = 1) : d181338 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17021, d181338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17021, d181338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15401 q = 1) (hb : d180908 q = 1) : d181339 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15401, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15401, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d17022 q = 1) (hb : d180908 q = 1) : d181340 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17022, d181340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17022, d181340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro55773 (p : Pattern) (ha : d20700 p = 1) (hb : d180908 p = 1) : d181366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17018 q = 1) (hb : d180908 q = 1) : d181333 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17018, d181333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55770 q ha hb
    | true =>
      simp only [d17018, d181333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55771 q ha hb
  have h2 (q : Pattern) (ha : d17019 q = 1) (hb : d180908 q = 1) : d181334 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17019, d181334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17019, d181334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17020 q = 1) (hb : d180908 q = 1) : d181335 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17020, d181335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17020, d181335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17023 q = 1) (hb : d180908 q = 1) : d181341 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17023, d181341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55771 q ha hb
    | true =>
      simp only [d17023, d181341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55772 q ha hb
  have h5 (q : Pattern) (ha : d17024 q = 1) (hb : d180908 q = 1) : d181342 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17024, d181342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17024, d181342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17025 q = 1) (hb : d180908 q = 1) : d181343 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17025, d181343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17025, d181343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17026 q = 1) (hb : d180908 q = 1) : d181344 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17026, d181344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17026, d181344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17033 q = 1) (hb : d180908 q = 1) : d181351 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55771 q ha hb
    | true =>
      simp only [d17033, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55761 q ha hb
  have h9 (q : Pattern) (ha : d17034 q = 1) (hb : d180908 q = 1) : d181352 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17035 q = 1) (hb : d180908 q = 1) : d181353 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17036 q = 1) (hb : d180908 q = 1) : d181361 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55761 q ha hb
    | true =>
      simp only [d17036, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55769 q ha hb
  have h12 (q : Pattern) (ha : d17037 q = 1) (hb : d180908 q = 1) : d181362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17038 q = 1) (hb : d180908 q = 1) : d181363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17039 q = 1) (hb : d180908 q = 1) : d181364 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17039, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17040 q = 1) (hb : d180908 q = 1) : d181365 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17040, d181365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17040, d181365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10092 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55765 q ha hb
    | true =>
      simp only [d10092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55766 q ha hb
  have h17 (q : Pattern) (ha : d10093 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10094 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10107 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55766 q ha hb
    | true =>
      simp only [d10107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55767 q ha hb
  have h20 (q : Pattern) (ha : d10108 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d10109 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d10110 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10122 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55766 q ha hb
    | true =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55758 q ha hb
  have h24 (q : Pattern) (ha : d10123 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d10123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d10124 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d10142 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55758 q ha hb
    | true =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55768 q ha hb
  have h27 (q : Pattern) (ha : d10143 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d10143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d10144 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d10145 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d10146 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d20700 q = 1) (hb : d180908 q = 1) : d181366 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20700, d181366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20700, d181366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro55774 (p : Pattern) (ha : d20703 p = 1) (hb : d180908 p = 1) : d181371 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d180908 q = 1) : d181351 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55771 q ha hb
    | true =>
      simp only [d17033, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55761 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d180908 q = 1) : d181352 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d180908 q = 1) : d181353 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d180908 q = 1) : d181361 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55761 q ha hb
    | true =>
      simp only [d17036, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55769 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d180908 q = 1) : d181362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d180908 q = 1) : d181363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d180908 q = 1) : d181364 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17044 q = 1) (hb : d180908 q = 1) : d181369 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17044, d181369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17044, d181369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17045 q = 1) (hb : d180908 q = 1) : d181370 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17045, d181370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17045, d181370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10122 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55766 q ha hb
    | true =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55758 q ha hb
  have h11 (q : Pattern) (ha : d10123 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10124 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10142 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55758 q ha hb
    | true =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55768 q ha hb
  have h14 (q : Pattern) (ha : d10143 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10144 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10145 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10150 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10151 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d20703 q = 1) (hb : d180908 q = 1) : d181371 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20703, d181371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20703, d181371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro55775 (p : Pattern) (ha : d20709 p = 1) (hb : d180908 p = 1) : d181377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20701 q = 1) (hb : d180908 q = 1) : d181367 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20701, d181367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55773 q ha hb
    | true =>
      simp only [d20701, d181367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20702 q = 1) (hb : d180908 q = 1) : d181368 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20702, d181368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20702, d181368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20704 q = 1) (hb : d180908 q = 1) : d181372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20704, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55774 q ha hb
    | true =>
      simp only [d20704, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20705 q = 1) (hb : d180908 q = 1) : d181373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20705, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20705, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20706 q = 1) (hb : d180908 q = 1) : d181374 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20706, d181374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20706, d181374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20707 q = 1) (hb : d180908 q = 1) : d181375 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20707, d181375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20707, d181375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20708 q = 1) (hb : d180908 q = 1) : d181376 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20708, d181376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20708, d181376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20709 q = 1) (hb : d180908 q = 1) : d181377 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20709, d181377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20709, d181377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55776 (p : Pattern) (ha : d20716 p = 1) (hb : d180908 p = 1) : d181393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20704 q = 1) (hb : d180908 q = 1) : d181372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20704, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55774 q ha hb
    | true =>
      simp only [d20704, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20705 q = 1) (hb : d180908 q = 1) : d181373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20705, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20705, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20711 q = 1) (hb : d180908 q = 1) : d181388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20711, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55762 q ha hb
    | true =>
      simp only [d20711, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20712 q = 1) (hb : d180908 q = 1) : d181389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20712, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20712, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20713 q = 1) (hb : d180908 q = 1) : d181390 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20713, d181390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20713, d181390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20714 q = 1) (hb : d180908 q = 1) : d181391 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20714, d181391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20714, d181391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20715 q = 1) (hb : d180908 q = 1) : d181392 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20715, d181392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20715, d181392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20716 q = 1) (hb : d180908 q = 1) : d181393 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20716, d181393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20716, d181393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55777 (p : Pattern) (ha : d10293 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10159 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10159, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10159, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1583 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10160 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10160, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10160, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10161 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10162 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d10293 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro55778 (p : Pattern) (ha : d13516 p = 1) (hb : d180908 p = 1) : d181396 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1868 q = 1) : d1868 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1869 q = 1) (hb : d131097 q = 1) : d19313 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d131097, d19313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1869, d131097, d19313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1583 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1870 q = 1) (hb : d180908 q = 1) : d181378 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d180908, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1870, d180908, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1871 q = 1) (hb : d180908 q = 1) : d181379 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1871, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1877 q = 1) (hb : d180908 q = 1) : d181380 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1877, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d13516 q = 1) (hb : d180908 q = 1) : d181396 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13516, d181396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13516, d181396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro55779 (p : Pattern) (ha : d20734 p = 1) (hb : d180908 p = 1) : d181402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d180908 q = 1) : d181351 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55771 q ha hb
    | true =>
      simp only [d17033, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55761 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d180908 q = 1) : d181352 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d180908 q = 1) : d181353 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d180908 q = 1) : d181361 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55761 q ha hb
    | true =>
      simp only [d17036, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55769 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d180908 q = 1) : d181362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d180908 q = 1) : d181363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d180908 q = 1) : d181364 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17108 q = 1) (hb : d180908 q = 1) : d181397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17108, d181397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55761 q ha hb
    | true =>
      simp only [d17108, d181397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55778 q ha hb
  have h9 (q : Pattern) (ha : d17109 q = 1) (hb : d180908 q = 1) : d181398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17109, d181398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17109, d181398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17110 q = 1) (hb : d180908 q = 1) : d181399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17110, d181399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17110, d181399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17111 q = 1) (hb : d180908 q = 1) : d181400 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17111, d181400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17111, d181400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d17112 q = 1) (hb : d180908 q = 1) : d181401 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17112, d181401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17112, d181401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10122 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55766 q ha hb
    | true =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55758 q ha hb
  have h14 (q : Pattern) (ha : d10123 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10124 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10142 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55758 q ha hb
    | true =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55768 q ha hb
  have h17 (q : Pattern) (ha : d10143 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10144 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10145 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10294 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55758 q ha hb
    | true =>
      simp only [d10294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55777 q ha hb
  have h21 (q : Pattern) (ha : d10295 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10296 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10297 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d10298 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d20734 q = 1) (hb : d180908 q = 1) : d181402 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20734, d181402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d20734, d181402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro55780 (p : Pattern) (ha : d20740 p = 1) (hb : d180908 p = 1) : d181408 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20735 q = 1) (hb : d180908 q = 1) : d181403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20735, d181403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55779 q ha hb
    | true =>
      simp only [d20735, d181403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20736 q = 1) (hb : d180908 q = 1) : d181404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20736, d181404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20736, d181404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20737 q = 1) (hb : d180908 q = 1) : d181405 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20737, d181405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20737, d181405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20738 q = 1) (hb : d180908 q = 1) : d181406 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20738, d181406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20738, d181406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20739 q = 1) (hb : d180908 q = 1) : d181407 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20739, d181407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20739, d181407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20740 q = 1) (hb : d180908 q = 1) : d181408 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20740, d181408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20740, d181408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55781 (p : Pattern) (ha : d131014 p = 1) (hb : d180908 p = 1) : d181414 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20717 q = 1) (hb : d180908 q = 1) : d181394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20717, d181394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55775 q ha hb
    | true =>
      simp only [d20717, d181394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55776 q ha hb
  have h2 (q : Pattern) (ha : d131010 q = 1) (hb : d180908 q = 1) : d181395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131010, d181395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131010, d181395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20741 q = 1) (hb : d180908 q = 1) : d181409 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20741, d181409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55780 q ha hb
    | true =>
      simp only [d20741, d181409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20742 q = 1) (hb : d180908 q = 1) : d181410 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20742, d181410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20742, d181410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131011 q = 1) (hb : d180908 q = 1) : d181411 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131011, d181411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131011, d181411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131012 q = 1) (hb : d180908 q = 1) : d181412 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131012, d181412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131012, d181412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131013 q = 1) (hb : d180908 q = 1) : d181413 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131013, d181413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131013, d181413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131014 q = 1) (hb : d180908 q = 1) : d181414 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131014, d181414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131014, d181414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55782 (p : Pattern) (ha : d131020 p = 1) (hb : d180908 p = 1) : d181431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131015 q = 1) (hb : d180908 q = 1) : d181415 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131015, d181415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131015, d181415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55781 q ha hb
  have h2 (q : Pattern) (ha : d20758 q = 1) (hb : d180908 q = 1) : d181426 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20758, d181426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20758, d181426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55764 q ha hb
  have h3 (q : Pattern) (ha : d131016 q = 1) (hb : d180908 q = 1) : d181427 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131016, d181427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131016, d181427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131017 q = 1) (hb : d180908 q = 1) : d181428 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131017, d181428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131017, d181428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131018 q = 1) (hb : d180908 q = 1) : d181429 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131018, d181429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131018, d181429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131019 q = 1) (hb : d180908 q = 1) : d181430 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131019, d181430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131019, d181430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d131020 q = 1) (hb : d180908 q = 1) : d181431 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131020, d181431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131020, d181431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro55783 (p : Pattern) (ha : d131026 p = 1) (hb : d180908 p = 1) : d181437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131021 q = 1) (hb : d180908 q = 1) : d181432 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131021, d181432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131021, d181432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55782 q ha hb
  have h2 (q : Pattern) (ha : d131022 q = 1) (hb : d180908 q = 1) : d181433 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131022, d181433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131022, d181433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131023 q = 1) (hb : d180908 q = 1) : d181434 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131023, d181434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131023, d181434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131024 q = 1) (hb : d180908 q = 1) : d181435 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131024, d181435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131024, d181435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131025 q = 1) (hb : d180908 q = 1) : d181436 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131025, d181436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131025, d181436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131026 q = 1) (hb : d180908 q = 1) : d181437 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131026, d181437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131026, d181437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55784 (p : Pattern) (ha : d10397 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2053 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10387 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10387, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10387, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2054 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10388 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10388, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10388, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10389 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d10391 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10392 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10392, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10392, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10393 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10394 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10394, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10394, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10395 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d10396 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d10371 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10372 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10372, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10372, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d10373 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10374 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10374, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10374, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d10375 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d10381 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h19 (q : Pattern) (ha : d10397 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro55785 (p : Pattern) (ha : d10440 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2065 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10436 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10436, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10436, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2066 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10437 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10437, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10437, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10438 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10439 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10412 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10413 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10413, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10413, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10414 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10415 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10415, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10415, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d10416 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d10417 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d10440 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro55786 (p : Pattern) (ha : d15813 p = 1) (hb : d180908 p = 1) : d181505 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2346 q = 1) : d2346 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2065 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2347 q = 1) (hb : d131097 q = 1) : d19545 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d131097, d19545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2347, d131097, d19545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2066 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2348 q = 1) (hb : d180908 q = 1) : d181502 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d180908, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2348, d180908, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2349 q = 1) (hb : d180908 q = 1) : d181503 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2349, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2355 q = 1) (hb : d180908 q = 1) : d181504 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2355, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d15790 q = 1) : d15790 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10412 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d131097 q = 1) : d19510 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d131097, d19510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d15791, d131097, d19510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d10414 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d15792 q = 1) (hb : d180908 q = 1) : d181481 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, d180908, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15792, d180908, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d15793 q = 1) (hb : d180908 q = 1) : d181482 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15793, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d15794 q = 1) (hb : d180908 q = 1) : d181483 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15794, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d15813 q = 1) (hb : d180908 q = 1) : d181505 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15813, d181505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15813, d181505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro55787 (p : Pattern) (ha : d17396 p = 1) (hb : d180908 p = 1) : d181474 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2340 q = 1) : d2340 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2053 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2341 q = 1) (hb : d131097 q = 1) : d19495 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d131097, d19495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2341, d131097, d19495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2054 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2342 q = 1) (hb : d180908 q = 1) : d181469 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d180908, d181469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2342, d180908, d181469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2343 q = 1) (hb : d180908 q = 1) : d181470 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d181470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2343, d181470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d17391 q = 1) : d17391 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10391 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17392 q = 1) (hb : d131097 q = 1) : d19498 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17392, d131097, d19498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d17392, d131097, d19498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10393 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d17393 q = 1) (hb : d180908 q = 1) : d181471 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17393, d180908, d181471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17393, d180908, d181471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d17394 q = 1) (hb : d180908 q = 1) : d181472 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17394, d181472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17394, d181472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d17395 q = 1) (hb : d180908 q = 1) : d181473 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17395, d181473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17395, d181473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1 q = 1) (hb : d15775 q = 1) : d15775 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d10371 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d15776 q = 1) (hb : d131097 q = 1) : d19481 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d131097, d19481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d15776, d131097, d19481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d10373 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d15777 q = 1) (hb : d180908 q = 1) : d181456 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d180908, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15777, d180908, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d15778 q = 1) (hb : d180908 q = 1) : d181457 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d15778, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h20 (q : Pattern) (ha : d15779 q = 1) (hb : d180908 q = 1) : d181463 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15779, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d15779, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h21 (q : Pattern) (ha : d17396 q = 1) (hb : d180908 q = 1) : d181474 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17396, d181474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17396, d181474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro55788 (p : Pattern) (ha : d20784 p = 1) (hb : d180908 p = 1) : d181511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17417 q = 1) (hb : d180908 q = 1) : d181506 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55787 q ha hb
    | true =>
      simp only [d17417, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55786 q ha hb
  have h2 (q : Pattern) (ha : d17418 q = 1) (hb : d180908 q = 1) : d181507 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17418, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17419 q = 1) (hb : d180908 q = 1) : d181508 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17420 q = 1) (hb : d180908 q = 1) : d181509 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17420, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17421 q = 1) (hb : d180908 q = 1) : d181510 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17421, d181510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17421, d181510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10441 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55784 q ha hb
    | true =>
      simp only [d10441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55785 q ha hb
  have h7 (q : Pattern) (ha : d10442 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10443 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10444 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10445 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20784 q = 1) (hb : d180908 q = 1) : d181511 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20784, d181511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20784, d181511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro55789 (p : Pattern) (ha : d20825 p = 1) (hb : d180908 p = 1) : d181543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20785 q = 1) (hb : d180908 q = 1) : d181512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20785, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55788 q ha hb
    | true =>
      simp only [d20785, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20786 q = 1) (hb : d180908 q = 1) : d181513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20786, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20786, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20822 q = 1) (hb : d180908 q = 1) : d181540 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20822, d181540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20822, d181540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20823 q = 1) (hb : d180908 q = 1) : d181541 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20823, d181541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20823, d181541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20824 q = 1) (hb : d180908 q = 1) : d181542 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20824, d181542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20824, d181542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20825 q = 1) (hb : d180908 q = 1) : d181543 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20825, d181543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20825, d181543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55790 (p : Pattern) (ha : d20831 p = 1) (hb : d180908 p = 1) : d181549 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20826 q = 1) (hb : d180908 q = 1) : d181544 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20826, d181544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55789 q ha hb
    | true =>
      simp only [d20826, d181544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20827 q = 1) (hb : d180908 q = 1) : d181545 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20827, d181545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20827, d181545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20828 q = 1) (hb : d180908 q = 1) : d181546 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20828, d181546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20828, d181546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20829 q = 1) (hb : d180908 q = 1) : d181547 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20829, d181547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20829, d181547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20830 q = 1) (hb : d180908 q = 1) : d181548 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20830, d181548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20830, d181548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20831 q = 1) (hb : d180908 q = 1) : d181549 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20831, d181549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20831, d181549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55791 (p : Pattern) (ha : d10359 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2144 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10339 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10339, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10339, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10340 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10340, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10340, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10341 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d10343 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10344 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10344, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10344, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10345 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10346 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10346, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10346, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10347 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d10348 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d10353 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10354 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10354, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10354, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d10355 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10356 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10356, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10356, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d10357 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d10358 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10359 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro55792 (p : Pattern) (ha : d10377 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2035 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10360 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10360, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10360, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2036 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10361 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10361, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10361, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10362 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d10364 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10365 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10365, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10365, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10366 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10367 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10367, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10367, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10368 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d10369 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d10353 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10354 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10354, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10354, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d10355 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10356 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10356, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10356, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d10357 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d10371 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d10372 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10372, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10372, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d10373 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d10374 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10374, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10374, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  have h22 (q : Pattern) (ha : d10375 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d10375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d10376 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d10377 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro55793 (p : Pattern) (ha : d10382 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10353 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10354 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10354, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10354, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10355 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10356 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10356, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10356, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10357 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d10371 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10372 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10372, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10372, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10373 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10374 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10374, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10374, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10375 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d10376 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10381 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d10382 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro55794 (p : Pattern) (ha : d10418 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5247 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10401 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10401, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10401, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5248 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10402 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10402, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10402, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10403 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10404 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10412 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10413 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10413, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10413, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10414 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10415 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10415, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10415, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d10416 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d10417 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d10418 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro55795 (p : Pattern) (ha : d15795 p = 1) (hb : d180908 p = 1) : d181484 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d6643 q = 1) : d6643 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5247 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6644 q = 1) (hb : d131097 q = 1) : d19506 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6644, d131097, d19506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6644, d131097, d19506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5248 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6645 q = 1) (hb : d180908 q = 1) : d181478 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6645, d180908, d181478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6645, d180908, d181478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6646 q = 1) (hb : d180908 q = 1) : d181479 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6646, d181479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6646, d181479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6647 q = 1) (hb : d180908 q = 1) : d181480 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6647, d181480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6647, d181480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d15790 q = 1) : d15790 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10412 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d131097 q = 1) : d19510 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d131097, d19510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d15791, d131097, d19510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d10414 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d15792 q = 1) (hb : d180908 q = 1) : d181481 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, d180908, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15792, d180908, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d15793 q = 1) (hb : d180908 q = 1) : d181482 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15793, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d15794 q = 1) (hb : d180908 q = 1) : d181483 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15794, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d15795 q = 1) (hb : d180908 q = 1) : d181484 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15795, d181484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15795, d181484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro55796 (p : Pattern) (ha : d17375 p = 1) (hb : d180908 p = 1) : d181450 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2331 q = 1) : d2331 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2144 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2332 q = 1) (hb : d131097 q = 1) : d19462 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2332, d131097, d19462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2332, d131097, d19462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2333 q = 1) (hb : d180908 q = 1) : d181442 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2333, d180908, d181442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2333, d180908, d181442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2334 q = 1) (hb : d180908 q = 1) : d181443 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2334, d181443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2334, d181443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d17369 q = 1) : d17369 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10343 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17370 q = 1) (hb : d131097 q = 1) : d19465 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17370, d131097, d19465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d17370, d131097, d19465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10345 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d17371 q = 1) (hb : d180908 q = 1) : d181444 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17371, d180908, d181444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17371, d180908, d181444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d17372 q = 1) (hb : d180908 q = 1) : d181445 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17372, d181445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17372, d181445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d17373 q = 1) (hb : d180908 q = 1) : d181446 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17373, d181446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17373, d181446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1 q = 1) (hb : d13813 q = 1) : d13813 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d10353 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d13814 q = 1) (hb : d131097 q = 1) : d19469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d131097, d19469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d13814, d131097, d19469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d10355 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d13815 q = 1) (hb : d180908 q = 1) : d181447 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d180908, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13815, d180908, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d13816 q = 1) (hb : d180908 q = 1) : d181448 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d13816, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h20 (q : Pattern) (ha : d17374 q = 1) (hb : d180908 q = 1) : d181449 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17374, d181449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17374, d181449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d17375 q = 1) (hb : d180908 q = 1) : d181450 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17375, d181450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17375, d181450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro55797 (p : Pattern) (ha : d17382 p = 1) (hb : d180908 p = 1) : d181459 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2335 q = 1) : d2335 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2035 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2336 q = 1) (hb : d131097 q = 1) : d19474 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, d131097, d19474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2336, d131097, d19474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2036 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2337 q = 1) (hb : d180908 q = 1) : d181451 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2337, d180908, d181451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2337, d180908, d181451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2338 q = 1) (hb : d180908 q = 1) : d181452 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2338, d181452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2338, d181452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d17376 q = 1) : d17376 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10364 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17377 q = 1) (hb : d131097 q = 1) : d19477 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d131097, d19477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d17377, d131097, d19477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10366 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d17378 q = 1) (hb : d180908 q = 1) : d181453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17378, d180908, d181453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17378, d180908, d181453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d17379 q = 1) (hb : d180908 q = 1) : d181454 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17379, d181454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17379, d181454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d17380 q = 1) (hb : d180908 q = 1) : d181455 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17380, d181455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17380, d181455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1 q = 1) (hb : d13813 q = 1) : d13813 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d10353 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d13814 q = 1) (hb : d131097 q = 1) : d19469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d131097, d19469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d13814, d131097, d19469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d10355 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d13815 q = 1) (hb : d180908 q = 1) : d181447 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d180908, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13815, d180908, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d13816 q = 1) (hb : d180908 q = 1) : d181448 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d13816, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h20 (q : Pattern) (ha : d1 q = 1) (hb : d15775 q = 1) : d15775 q = 1 := by
    exact hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d10371 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d15776 q = 1) (hb : d131097 q = 1) : d19481 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d131097, d19481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d15776, d131097, d19481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d10373 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d15777 q = 1) (hb : d180908 q = 1) : d181456 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d180908, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d15777, d180908, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d15778 q = 1) (hb : d180908 q = 1) : d181457 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d15778, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h26 (q : Pattern) (ha : d17381 q = 1) (hb : d180908 q = 1) : d181458 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17381, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d17381, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d17382 q = 1) (hb : d180908 q = 1) : d181459 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17382, d181459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17382, d181459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro55798 (p : Pattern) (ha : d17386 p = 1) (hb : d180908 p = 1) : d181464 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d13813 q = 1) : d13813 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10353 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13814 q = 1) (hb : d131097 q = 1) : d19469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d131097, d19469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13814, d131097, d19469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10355 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13815 q = 1) (hb : d180908 q = 1) : d181447 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d180908, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13815, d180908, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13816 q = 1) (hb : d180908 q = 1) : d181448 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13816, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d15775 q = 1) : d15775 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15776 q = 1) (hb : d131097 q = 1) : d19481 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d131097, d19481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d15776, d131097, d19481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10373 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15777 q = 1) (hb : d180908 q = 1) : d181456 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d180908, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15777, d180908, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d15778 q = 1) (hb : d180908 q = 1) : d181457 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15778, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d17381 q = 1) (hb : d180908 q = 1) : d181458 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17381, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17381, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15779 q = 1) (hb : d180908 q = 1) : d181463 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15779, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15779, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d17386 q = 1) (hb : d180908 q = 1) : d181464 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17386, d181464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17386, d181464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro55799 (p : Pattern) (ha : d20774 p = 1) (hb : d180908 p = 1) : d181490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17383 q = 1) (hb : d180908 q = 1) : d181460 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17383, d181460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55796 q ha hb
    | true =>
      simp only [d17383, d181460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55797 q ha hb
  have h2 (q : Pattern) (ha : d17384 q = 1) (hb : d180908 q = 1) : d181461 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17384, d181461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17384, d181461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17385 q = 1) (hb : d180908 q = 1) : d181462 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17385, d181462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17385, d181462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17387 q = 1) (hb : d180908 q = 1) : d181465 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17387, d181465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55797 q ha hb
    | true =>
      simp only [d17387, d181465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55798 q ha hb
  have h5 (q : Pattern) (ha : d17388 q = 1) (hb : d180908 q = 1) : d181466 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17388, d181466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17388, d181466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17389 q = 1) (hb : d180908 q = 1) : d181467 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17389, d181467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17389, d181467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17390 q = 1) (hb : d180908 q = 1) : d181468 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17390, d181468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17390, d181468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17397 q = 1) (hb : d180908 q = 1) : d181475 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55797 q ha hb
    | true =>
      simp only [d17397, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55787 q ha hb
  have h9 (q : Pattern) (ha : d17398 q = 1) (hb : d180908 q = 1) : d181476 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17399 q = 1) (hb : d180908 q = 1) : d181477 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17400 q = 1) (hb : d180908 q = 1) : d181485 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55787 q ha hb
    | true =>
      simp only [d17400, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55795 q ha hb
  have h12 (q : Pattern) (ha : d17401 q = 1) (hb : d180908 q = 1) : d181486 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17402 q = 1) (hb : d180908 q = 1) : d181487 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17403 q = 1) (hb : d180908 q = 1) : d181488 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17403, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17404 q = 1) (hb : d180908 q = 1) : d181489 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17404, d181489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17404, d181489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10378 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55791 q ha hb
    | true =>
      simp only [d10378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55792 q ha hb
  have h17 (q : Pattern) (ha : d10379 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10380 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10383 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55792 q ha hb
    | true =>
      simp only [d10383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55793 q ha hb
  have h20 (q : Pattern) (ha : d10384 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d10385 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d10386 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10398 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55792 q ha hb
    | true =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55784 q ha hb
  have h24 (q : Pattern) (ha : d10399 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d10399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d10400 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d10419 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55784 q ha hb
    | true =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55794 q ha hb
  have h27 (q : Pattern) (ha : d10420 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d10420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d10421 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d10422 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d10423 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d20774 q = 1) (hb : d180908 q = 1) : d181490 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20774, d181490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20774, d181490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro55800 (p : Pattern) (ha : d20777 p = 1) (hb : d180908 p = 1) : d181495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d180908 q = 1) : d181475 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55797 q ha hb
    | true =>
      simp only [d17397, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55787 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d180908 q = 1) : d181476 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d180908 q = 1) : d181477 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d180908 q = 1) : d181485 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55787 q ha hb
    | true =>
      simp only [d17400, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55795 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d180908 q = 1) : d181486 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d180908 q = 1) : d181487 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d180908 q = 1) : d181488 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17408 q = 1) (hb : d180908 q = 1) : d181493 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17408, d181493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17408, d181493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17409 q = 1) (hb : d180908 q = 1) : d181494 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17409, d181494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17409, d181494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10398 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55792 q ha hb
    | true =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55784 q ha hb
  have h11 (q : Pattern) (ha : d10399 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10400 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10419 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55784 q ha hb
    | true =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55794 q ha hb
  have h14 (q : Pattern) (ha : d10420 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10421 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10422 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10427 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10428 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d20777 q = 1) (hb : d180908 q = 1) : d181495 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20777, d181495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20777, d181495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro55801 (p : Pattern) (ha : d20783 p = 1) (hb : d180908 p = 1) : d181501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20775 q = 1) (hb : d180908 q = 1) : d181491 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20775, d181491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55799 q ha hb
    | true =>
      simp only [d20775, d181491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20776 q = 1) (hb : d180908 q = 1) : d181492 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20776, d181492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20776, d181492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20778 q = 1) (hb : d180908 q = 1) : d181496 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20778, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55800 q ha hb
    | true =>
      simp only [d20778, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20779 q = 1) (hb : d180908 q = 1) : d181497 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20779, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20779, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20780 q = 1) (hb : d180908 q = 1) : d181498 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20780, d181498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20780, d181498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20781 q = 1) (hb : d180908 q = 1) : d181499 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20781, d181499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20781, d181499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20782 q = 1) (hb : d180908 q = 1) : d181500 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20782, d181500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20782, d181500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20783 q = 1) (hb : d180908 q = 1) : d181501 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20783, d181501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20783, d181501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55802 (p : Pattern) (ha : d20790 p = 1) (hb : d180908 p = 1) : d181517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20778 q = 1) (hb : d180908 q = 1) : d181496 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20778, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55800 q ha hb
    | true =>
      simp only [d20778, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20779 q = 1) (hb : d180908 q = 1) : d181497 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20779, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20779, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20785 q = 1) (hb : d180908 q = 1) : d181512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20785, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55788 q ha hb
    | true =>
      simp only [d20785, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20786 q = 1) (hb : d180908 q = 1) : d181513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20786, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20786, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20787 q = 1) (hb : d180908 q = 1) : d181514 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20787, d181514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20787, d181514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20788 q = 1) (hb : d180908 q = 1) : d181515 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20788, d181515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20788, d181515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20789 q = 1) (hb : d180908 q = 1) : d181516 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20789, d181516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20789, d181516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20790 q = 1) (hb : d180908 q = 1) : d181517 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20790, d181517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20790, d181517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55803 (p : Pattern) (ha : d10559 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2065 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10436 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10436, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10436, d131097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2066 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10437 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10437, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10437, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10438 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10439 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d10559 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro55804 (p : Pattern) (ha : d13843 p = 1) (hb : d180908 p = 1) : d181520 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2346 q = 1) : d2346 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2065 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2347 q = 1) (hb : d131097 q = 1) : d19545 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d131097, d19545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2347, d131097, d19545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2066 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2348 q = 1) (hb : d180908 q = 1) : d181502 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d180908, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2348, d180908, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2349 q = 1) (hb : d180908 q = 1) : d181503 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2349, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2355 q = 1) (hb : d180908 q = 1) : d181504 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2355, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d13843 q = 1) (hb : d180908 q = 1) : d181520 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13843, d181520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13843, d181520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro55805 (p : Pattern) (ha : d20808 p = 1) (hb : d180908 p = 1) : d181526 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d180908 q = 1) : d181475 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55797 q ha hb
    | true =>
      simp only [d17397, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55787 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d180908 q = 1) : d181476 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d180908 q = 1) : d181477 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d180908 q = 1) : d181485 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55787 q ha hb
    | true =>
      simp only [d17400, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55795 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d180908 q = 1) : d181486 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d180908 q = 1) : d181487 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d180908 q = 1) : d181488 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17472 q = 1) (hb : d180908 q = 1) : d181521 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17472, d181521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55787 q ha hb
    | true =>
      simp only [d17472, d181521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55804 q ha hb
  have h9 (q : Pattern) (ha : d17473 q = 1) (hb : d180908 q = 1) : d181522 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17473, d181522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17473, d181522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17474 q = 1) (hb : d180908 q = 1) : d181523 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17474, d181523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17474, d181523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17475 q = 1) (hb : d180908 q = 1) : d181524 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17475, d181524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17475, d181524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d17476 q = 1) (hb : d180908 q = 1) : d181525 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17476, d181525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17476, d181525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10398 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55792 q ha hb
    | true =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55784 q ha hb
  have h14 (q : Pattern) (ha : d10399 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10400 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10419 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55784 q ha hb
    | true =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55794 q ha hb
  have h17 (q : Pattern) (ha : d10420 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10421 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10422 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10560 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55784 q ha hb
    | true =>
      simp only [d10560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55803 q ha hb
  have h21 (q : Pattern) (ha : d10561 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10562 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10563 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d10564 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d20808 q = 1) (hb : d180908 q = 1) : d181526 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20808, d181526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d20808, d181526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro55806 (p : Pattern) (ha : d20814 p = 1) (hb : d180908 p = 1) : d181532 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20809 q = 1) (hb : d180908 q = 1) : d181527 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20809, d181527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55805 q ha hb
    | true =>
      simp only [d20809, d181527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20810 q = 1) (hb : d180908 q = 1) : d181528 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20810, d181528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20810, d181528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20811 q = 1) (hb : d180908 q = 1) : d181529 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20811, d181529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20811, d181529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20812 q = 1) (hb : d180908 q = 1) : d181530 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20812, d181530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20812, d181530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20813 q = 1) (hb : d180908 q = 1) : d181531 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20813, d181531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20813, d181531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20814 q = 1) (hb : d180908 q = 1) : d181532 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20814, d181532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20814, d181532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55807 (p : Pattern) (ha : d131035 p = 1) (hb : d180908 p = 1) : d181538 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20791 q = 1) (hb : d180908 q = 1) : d181518 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20791, d181518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55801 q ha hb
    | true =>
      simp only [d20791, d181518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55802 q ha hb
  have h2 (q : Pattern) (ha : d131031 q = 1) (hb : d180908 q = 1) : d181519 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131031, d181519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131031, d181519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20815 q = 1) (hb : d180908 q = 1) : d181533 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20815, d181533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55806 q ha hb
    | true =>
      simp only [d20815, d181533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20816 q = 1) (hb : d180908 q = 1) : d181534 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20816, d181534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20816, d181534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131032 q = 1) (hb : d180908 q = 1) : d181535 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131032, d181535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131032, d181535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131033 q = 1) (hb : d180908 q = 1) : d181536 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131033, d181536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131033, d181536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131034 q = 1) (hb : d180908 q = 1) : d181537 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131034, d181537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131034, d181537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131035 q = 1) (hb : d180908 q = 1) : d181538 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131035, d181538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131035, d181538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55808 (p : Pattern) (ha : d131041 p = 1) (hb : d180908 p = 1) : d181555 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131036 q = 1) (hb : d180908 q = 1) : d181539 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131036, d181539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131036, d181539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55807 q ha hb
  have h2 (q : Pattern) (ha : d20832 q = 1) (hb : d180908 q = 1) : d181550 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20832, d181550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20832, d181550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55790 q ha hb
  have h3 (q : Pattern) (ha : d131037 q = 1) (hb : d180908 q = 1) : d181551 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131037, d181551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131037, d181551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131038 q = 1) (hb : d180908 q = 1) : d181552 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131038, d181552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131038, d181552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131039 q = 1) (hb : d180908 q = 1) : d181553 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131039, d181553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131039, d181553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131040 q = 1) (hb : d180908 q = 1) : d181554 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131040, d181554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131040, d181554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d131041 q = 1) (hb : d180908 q = 1) : d181555 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131041, d181555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131041, d181555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro55809 (p : Pattern) (ha : d131047 p = 1) (hb : d180908 p = 1) : d181561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131042 q = 1) (hb : d180908 q = 1) : d181556 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131042, d181556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131042, d181556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55808 q ha hb
  have h2 (q : Pattern) (ha : d131043 q = 1) (hb : d180908 q = 1) : d181557 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131043, d181557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131043, d181557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131044 q = 1) (hb : d180908 q = 1) : d181558 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131044, d181558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131044, d181558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131045 q = 1) (hb : d180908 q = 1) : d181559 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131045, d181559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131045, d181559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131046 q = 1) (hb : d180908 q = 1) : d181560 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131046, d181560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131046, d181560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131047 q = 1) (hb : d180908 q = 1) : d181561 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131047, d181561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131047, d181561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55810 (p : Pattern) (ha : d131053 p = 1) (hb : d180908 p = 1) : d181567 p = 1 := by
  have h0 (q : Pattern) (ha : d130970 q = 1) (hb : d180908 q = 1) : d181096 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130970, d181096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55695 q ha hb
    | true =>
      simp only [d130970, d181096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55710 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130988 q = 1) (hb : d180908 q = 1) : d181185 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130988, d181185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130988, d181185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55731 q ha hb
  have h3 (q : Pattern) (ha : d130989 q = 1) (hb : d180908 q = 1) : d181186 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130989, d181186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130989, d181186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131007 q = 1) (hb : d180908 q = 1) : d181310 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131007, d181310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131007, d181310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55757 q ha hb
  have h5 (q : Pattern) (ha : d131008 q = 1) (hb : d180908 q = 1) : d181311 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131008, d181311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131008, d181311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131009 q = 1) (hb : d180908 q = 1) : d181312 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131009, d181312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131009, d181312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131027 q = 1) (hb : d180908 q = 1) : d181438 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131027, d181438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131027, d181438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55783 q ha hb
  have h8 (q : Pattern) (ha : d131028 q = 1) (hb : d180908 q = 1) : d181439 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131028, d181439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131028, d181439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131029 q = 1) (hb : d180908 q = 1) : d181440 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131029, d181440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131029, d181440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131030 q = 1) (hb : d180908 q = 1) : d181441 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131030, d181441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131030, d181441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131048 q = 1) (hb : d180908 q = 1) : d181562 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131048, d181562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131048, d181562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55809 q ha hb
  have h12 (q : Pattern) (ha : d131049 q = 1) (hb : d180908 q = 1) : d181563 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131049, d181563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131049, d181563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d131050 q = 1) (hb : d180908 q = 1) : d181564 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131050, d181564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131050, d181564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131051 q = 1) (hb : d180908 q = 1) : d181565 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131051, d181565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131051, d181565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d131052 q = 1) (hb : d180908 q = 1) : d181566 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d131052, d181566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131052, d181566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d131053 q = 1) (hb : d180908 q = 1) : d181567 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d131053, d181567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131053, d181567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro55811 (p : Pattern) (ha : d131059 p = 1) (hb : d180908 p = 1) : d181573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131054 q = 1) (hb : d180908 q = 1) : d181568 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d131054, d181568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55810 q ha hb
    | true =>
      simp only [d131054, d181568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131055 q = 1) (hb : d180908 q = 1) : d181569 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d131055, d181569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131055, d181569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131056 q = 1) (hb : d180908 q = 1) : d181570 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d131056, d181570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131056, d181570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131057 q = 1) (hb : d180908 q = 1) : d181571 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d131057, d181571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131057, d181571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131058 q = 1) (hb : d180908 q = 1) : d181572 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d131058, d181572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131058, d181572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131059 q = 1) (hb : d180908 q = 1) : d181573 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d131059, d181573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131059, d181573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55812 (p : Pattern) (ha : d131065 p = 1) (hb : d180908 p = 1) : d181579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131060 q = 1) (hb : d180908 q = 1) : d181574 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d131060, d181574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55811 q ha hb
    | true =>
      simp only [d131060, d181574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131061 q = 1) (hb : d180908 q = 1) : d181575 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d131061, d181575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131061, d181575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131062 q = 1) (hb : d180908 q = 1) : d181576 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d131062, d181576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131062, d181576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131063 q = 1) (hb : d180908 q = 1) : d181577 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d131063, d181577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131063, d181577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131064 q = 1) (hb : d180908 q = 1) : d181578 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d131064, d181578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131064, d181578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131065 q = 1) (hb : d180908 q = 1) : d181579 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d131065, d181579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131065, d181579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55813 (p : Pattern) (ha : d131071 p = 1) (hb : d187676 p = 1) : d181585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131066 q = 1) (hb : d180908 q = 1) : d181580 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d131066, d181580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55812 q ha hb
    | true =>
      simp only [d131066, d181580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131067 q = 1) (hb : d180908 q = 1) : d181581 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d131067, d181581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131067, d181581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131068 q = 1) (hb : d180908 q = 1) : d181582 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d131068, d181582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131068, d181582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131069 q = 1) (hb : d180908 q = 1) : d181583 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d131069, d181583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131069, d181583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d131070 q = 1) (hb : d187676 q = 1) : d181584 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d131070, d187676, d181584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131070, d187676, d181584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d187676 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d131071 q = 1) (hb : d187676 q = 1) : d181585 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d131071, d181585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131071, d181585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55814 (p : Pattern) (ha : d131077 p = 1) (hb : d187676 p = 1) : d181591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d187676 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131072 q = 1) (hb : d187676 q = 1) : d181586 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d131072, d181586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55813 q ha hb
    | true =>
      simp only [d131072, d181586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131073 q = 1) (hb : d187676 q = 1) : d181587 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d131073, d181587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131073, d181587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131074 q = 1) (hb : d187676 q = 1) : d181588 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d131074, d181588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131074, d181588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131075 q = 1) (hb : d187676 q = 1) : d181589 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d131075, d181589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131075, d181589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131076 q = 1) (hb : d187676 q = 1) : d181590 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d131076, d181590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131076, d181590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131077 q = 1) (hb : d187676 q = 1) : d181591 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d131077, d181591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131077, d181591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55815 (p : Pattern) (ha : d131083 p = 1) (hb : d187676 p = 1) : d181597 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d187676 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131078 q = 1) (hb : d187676 q = 1) : d181592 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d131078, d181592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55814 q ha hb
    | true =>
      simp only [d131078, d181592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131079 q = 1) (hb : d187676 q = 1) : d181593 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d131079, d181593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131079, d181593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131080 q = 1) (hb : d187676 q = 1) : d181594 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d131080, d181594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131080, d181594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131081 q = 1) (hb : d187676 q = 1) : d181595 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d131081, d181595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131081, d181595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131082 q = 1) (hb : d187676 q = 1) : d181596 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d131082, d181596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131082, d181596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131083 q = 1) (hb : d187676 q = 1) : d181597 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d131083, d181597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131083, d181597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55816 (p : Pattern) (ha : d131089 p = 1) (hb : d187676 p = 1) : d181603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d187676 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131084 q = 1) (hb : d187676 q = 1) : d181598 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d131084, d181598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55815 q ha hb
    | true =>
      simp only [d131084, d181598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131085 q = 1) (hb : d187676 q = 1) : d181599 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d131085, d181599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131085, d181599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131086 q = 1) (hb : d187676 q = 1) : d181600 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d131086, d181600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131086, d181600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131087 q = 1) (hb : d187676 q = 1) : d181601 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d131087, d181601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131087, d181601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131088 q = 1) (hb : d187676 q = 1) : d181602 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d131088, d181602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131088, d181602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131089 q = 1) (hb : d187676 q = 1) : d181603 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d131089, d181603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131089, d181603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55817 (p : Pattern) (ha : d131095 p = 1) (hb : d187676 p = 1) : d181609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d187676 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131090 q = 1) (hb : d187676 q = 1) : d181604 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d131090, d181604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55816 q ha hb
    | true =>
      simp only [d131090, d181604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131091 q = 1) (hb : d187676 q = 1) : d181605 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d131091, d181605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131091, d181605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131092 q = 1) (hb : d187676 q = 1) : d181606 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d131092, d181606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131092, d181606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131093 q = 1) (hb : d187676 q = 1) : d181607 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d131093, d181607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131093, d181607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131094 q = 1) (hb : d187676 q = 1) : d181608 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d131094, d181608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131094, d181608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131095 q = 1) (hb : d187676 q = 1) : d181609 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d131095, d181609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131095, d181609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55818 (p : Pattern) (ha : d180908 p = 1) (hb : d192722 p = 1) : d181614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20478 q = 1) (hb : d180908 q = 1) : d181011 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20478, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20478, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55687 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192718 q = 1) : d181610 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192718, d181610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192718, d181610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192719 q = 1) : d181611 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192719, d181611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192719, d181611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192720 q = 1) : d181612 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192720, d181612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192720, d181612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192721 q = 1) : d181613 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192721, d181613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192721, d181613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192722 q = 1) : d181614 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192722, d181614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192722, d181614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55819 (p : Pattern) (ha : d180908 p = 1) (hb : d192732 p = 1) : d181624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20420 q = 1) (hb : d180908 q = 1) : d180957 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20420, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55684 q ha hb
    | true =>
      simp only [d20420, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55678 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192728 q = 1) : d181620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192728, d181620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192728, d181620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192729 q = 1) : d181621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192729, d181621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192729, d181621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192730 q = 1) : d181622 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192730, d181622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192730, d181622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192731 q = 1) : d181623 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192731, d181623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192731, d181623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192732 q = 1) : d181624 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192732, d181624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192732, d181624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55820 (p : Pattern) (ha : d180908 p = 1) (hb : d192738 p = 1) : d181630 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192733 q = 1) : d181625 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192733, d181625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192733, d181625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55819 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192734 q = 1) : d181626 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192734, d181626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192734, d181626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192735 q = 1) : d181627 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192735, d181627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192735, d181627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192736 q = 1) : d181628 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192736, d181628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192736, d181628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192737 q = 1) : d181629 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192737, d181629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192737, d181629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192738 q = 1) : d181630 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192738, d181630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192738, d181630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55821 (p : Pattern) (ha : d180908 p = 1) (hb : d192744 p = 1) : d181636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192723 q = 1) : d181615 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192723, d181615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192723, d181615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55818 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192724 q = 1) : d181616 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192724, d181616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192724, d181616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192725 q = 1) : d181617 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192725, d181617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192725, d181617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192726 q = 1) : d181618 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192726, d181618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192726, d181618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192727 q = 1) : d181619 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192727, d181619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192727, d181619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192739 q = 1) : d181631 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192739, d181631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192739, d181631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55820 q ha hb
  have h7 (q : Pattern) (ha : d180908 q = 1) (hb : d192740 q = 1) : d181632 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192740, d181632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192740, d181632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d180908 q = 1) (hb : d192741 q = 1) : d181633 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192741, d181633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192741, d181633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d180908 q = 1) (hb : d192742 q = 1) : d181634 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192742, d181634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192742, d181634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d180908 q = 1) (hb : d192743 q = 1) : d181635 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192743, d181635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192743, d181635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d180908 q = 1) (hb : d192744 q = 1) : d181636 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192744, d181636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192744, d181636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro55822 (p : Pattern) (ha : d180908 p = 1) (hb : d192750 p = 1) : d181642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192745 q = 1) : d181637 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192745, d181637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55706 q hb ha
    | true =>
      simp only [d192745, d181637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55697 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192746 q = 1) : d181638 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192746, d181638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192746, d181638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192747 q = 1) : d181639 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192747, d181639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192747, d181639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192748 q = 1) : d181640 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192748, d181640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192748, d181640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192749 q = 1) : d181641 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192749, d181641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192749, d181641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192750 q = 1) : d181642 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192750, d181642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192750, d181642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55823 (p : Pattern) (ha : d180908 p = 1) (hb : d192756 p = 1) : d181648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192751 q = 1) : d181643 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192751, d181643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192751, d181643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55822 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192752 q = 1) : d181644 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192752, d181644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192752, d181644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192753 q = 1) : d181645 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192753, d181645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192753, d181645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192754 q = 1) : d181646 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192754, d181646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192754, d181646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192755 q = 1) : d181647 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192755, d181647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192755, d181647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192756 q = 1) : d181648 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192756, d181648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192756, d181648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55824 (p : Pattern) (ha : d180908 p = 1) (hb : d192762 p = 1) : d181654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192757 q = 1) : d181649 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192757, d181649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192757, d181649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55823 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192758 q = 1) : d181650 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192758, d181650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192758, d181650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192759 q = 1) : d181651 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192759, d181651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192759, d181651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192760 q = 1) : d181652 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192760, d181652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192760, d181652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192761 q = 1) : d181653 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192761, d181653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192761, d181653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192762 q = 1) : d181654 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192762, d181654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192762, d181654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55825 (p : Pattern) (ha : d180908 p = 1) (hb : d192769 p = 1) : d181661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192764 q = 1) : d181656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192764, d181656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55727 q hb ha
    | true =>
      simp only [d192764, d181656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55716 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192765 q = 1) : d181657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192765, d181657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192765, d181657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192766 q = 1) : d181658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192766, d181658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192766, d181658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192767 q = 1) : d181659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192767, d181659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192767, d181659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192768 q = 1) : d181660 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192768, d181660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192768, d181660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192769 q = 1) : d181661 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192769, d181661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192769, d181661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55826 (p : Pattern) (ha : d180908 p = 1) (hb : d192775 p = 1) : d181667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192770 q = 1) : d181662 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192770, d181662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192770, d181662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55825 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192771 q = 1) : d181663 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192771, d181663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192771, d181663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192772 q = 1) : d181664 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192772, d181664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192772, d181664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192773 q = 1) : d181665 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192773, d181665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192773, d181665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192774 q = 1) : d181666 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192774, d181666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192774, d181666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192775 q = 1) : d181667 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192775, d181667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192775, d181667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55827 (p : Pattern) (ha : d180908 p = 1) (hb : d192781 p = 1) : d181673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192776 q = 1) : d181668 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192776, d181668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192776, d181668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55826 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192777 q = 1) : d181669 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192777, d181669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192777, d181669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192778 q = 1) : d181670 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192778, d181670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192778, d181670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192779 q = 1) : d181671 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192779, d181671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192779, d181671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192780 q = 1) : d181672 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192780, d181672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192780, d181672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192781 q = 1) : d181673 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192781, d181673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192781, d181673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55828 (p : Pattern) (ha : d180908 p = 1) (hb : d192784 p = 1) : d181677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d180908 q = 1) : d181225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55745 q ha hb
    | true =>
      simp only [d16673, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55735 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d180908 q = 1) : d181226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d180908 q = 1) : d181227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d180908 q = 1) : d181235 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55735 q ha hb
    | true =>
      simp only [d16676, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55743 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d180908 q = 1) : d181236 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d180908 q = 1) : d181237 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d180908 q = 1) : d181238 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16693 q = 1) (hb : d180908 q = 1) : d181254 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55735 q ha hb
    | true =>
      simp only [d16693, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55734 q ha hb
  have h9 (q : Pattern) (ha : d16694 q = 1) (hb : d180908 q = 1) : d181255 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16695 q = 1) (hb : d180908 q = 1) : d181256 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16696 q = 1) (hb : d180908 q = 1) : d181257 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16696, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171139 q = 1) (hb : d180908 q = 1) : d181676 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171139, d181676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171139, d181676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9834 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55740 q ha hb
    | true =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55732 q ha hb
  have h14 (q : Pattern) (ha : d9835 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9836 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9851 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55732 q ha hb
    | true =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55742 q ha hb
  have h17 (q : Pattern) (ha : d9852 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9853 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9854 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9870 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55732 q ha hb
    | true =>
      simp only [d9870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55733 q ha hb
  have h21 (q : Pattern) (ha : d9871 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d9872 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9873 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d129539 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d129539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d180908 q = 1) (hb : d192784 q = 1) : d181677 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d192784, d181677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d192784, d181677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  exact h25 p ha hb
theorem andIntro55829 (p : Pattern) (ha : d180908 p = 1) (hb : d192790 p = 1) : d181683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192785 q = 1) : d181678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d192785, d181678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55828 q ha hb
    | true =>
      simp only [d192785, d181678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192786 q = 1) : d181679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d192786, d181679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192786, d181679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20638 q = 1) (hb : d180908 q = 1) : d181260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20638, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55736 q ha hb
    | true =>
      simp only [d20638, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20639 q = 1) (hb : d180908 q = 1) : d181261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20639, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20639, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192787 q = 1) : d181680 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d192787, d181680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192787, d181680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192788 q = 1) : d181681 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d192788, d181681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192788, d181681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d180908 q = 1) (hb : d192789 q = 1) : d181682 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d192789, d181682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192789, d181682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d180908 q = 1) (hb : d192790 q = 1) : d181683 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d192790, d181683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192790, d181683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro55830 (p : Pattern) (ha : d180908 p = 1) (hb : d192796 p = 1) : d181689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192791 q = 1) : d181684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192791, d181684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55829 q ha hb
    | true =>
      simp only [d192791, d181684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55737 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192792 q = 1) : d181685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192792, d181685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192792, d181685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192793 q = 1) : d181686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192793, d181686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192793, d181686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192794 q = 1) : d181687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192794, d181687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192794, d181687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192795 q = 1) : d181688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192795, d181688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192795, d181688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192796 q = 1) : d181689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192796, d181689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192796, d181689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55831 (p : Pattern) (ha : d180908 p = 1) (hb : d192802 p = 1) : d181695 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192797 q = 1) : d181690 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192797, d181690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192797, d181690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55830 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192798 q = 1) : d181691 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192798, d181691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192798, d181691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192799 q = 1) : d181692 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192799, d181692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192799, d181692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192800 q = 1) : d181693 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192800, d181693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192800, d181693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192801 q = 1) : d181694 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192801, d181694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192801, d181694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192802 q = 1) : d181695 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192802, d181695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192802, d181695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55832 (p : Pattern) (ha : d180908 p = 1) (hb : d192808 p = 1) : d181701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192803 q = 1) : d181696 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192803, d181696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192803, d181696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55831 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192804 q = 1) : d181697 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192804, d181697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192804, d181697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192805 q = 1) : d181698 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192805, d181698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192805, d181698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192806 q = 1) : d181699 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192806, d181699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192806, d181699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192807 q = 1) : d181700 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192807, d181700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192807, d181700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192808 q = 1) : d181701 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192808, d181701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192808, d181701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55833 (p : Pattern) (ha : d180908 p = 1) (hb : d192812 p = 1) : d181706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d180908 q = 1) : d181351 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55771 q ha hb
    | true =>
      simp only [d17033, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55761 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d180908 q = 1) : d181352 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d180908 q = 1) : d181353 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d180908 q = 1) : d181361 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55761 q ha hb
    | true =>
      simp only [d17036, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55769 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d180908 q = 1) : d181362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d180908 q = 1) : d181363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d180908 q = 1) : d181364 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17053 q = 1) (hb : d180908 q = 1) : d181382 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55761 q ha hb
    | true =>
      simp only [d17053, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55760 q ha hb
  have h9 (q : Pattern) (ha : d17054 q = 1) (hb : d180908 q = 1) : d181383 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17054, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17055 q = 1) (hb : d180908 q = 1) : d181384 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17056 q = 1) (hb : d180908 q = 1) : d181385 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17056, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171176 q = 1) (hb : d180908 q = 1) : d181705 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171176, d181705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171176, d181705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10122 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55766 q ha hb
    | true =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55758 q ha hb
  have h14 (q : Pattern) (ha : d10123 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10124 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10142 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55758 q ha hb
    | true =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55768 q ha hb
  have h17 (q : Pattern) (ha : d10143 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10144 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10145 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10164 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55758 q ha hb
    | true =>
      simp only [d10164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55759 q ha hb
  have h21 (q : Pattern) (ha : d10165 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10166 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10167 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d129568 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d129568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d180908 q = 1) (hb : d192812 q = 1) : d181706 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d192812, d181706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d192812, d181706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  exact h25 p ha hb
theorem andIntro55834 (p : Pattern) (ha : d180908 p = 1) (hb : d192818 p = 1) : d181712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192813 q = 1) : d181707 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d192813, d181707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55833 q ha hb
    | true =>
      simp only [d192813, d181707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192814 q = 1) : d181708 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d192814, d181708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192814, d181708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20711 q = 1) (hb : d180908 q = 1) : d181388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20711, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55762 q ha hb
    | true =>
      simp only [d20711, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20712 q = 1) (hb : d180908 q = 1) : d181389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20712, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20712, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192815 q = 1) : d181709 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d192815, d181709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192815, d181709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192816 q = 1) : d181710 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d192816, d181710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192816, d181710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d180908 q = 1) (hb : d192817 q = 1) : d181711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d192817, d181711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192817, d181711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d180908 q = 1) (hb : d192818 q = 1) : d181712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d192818, d181712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192818, d181712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro55835 (p : Pattern) (ha : d180908 p = 1) (hb : d192824 p = 1) : d181718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192819 q = 1) : d181713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192819, d181713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55834 q ha hb
    | true =>
      simp only [d192819, d181713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55763 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192820 q = 1) : d181714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192820, d181714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192820, d181714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192821 q = 1) : d181715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192821, d181715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192821, d181715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192822 q = 1) : d181716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192822, d181716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192822, d181716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192823 q = 1) : d181717 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192823, d181717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192823, d181717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192824 q = 1) : d181718 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192824, d181718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192824, d181718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55836 (p : Pattern) (ha : d180908 p = 1) (hb : d192830 p = 1) : d181724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192825 q = 1) : d181719 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192825, d181719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192825, d181719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55835 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192826 q = 1) : d181720 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192826, d181720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192826, d181720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192827 q = 1) : d181721 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192827, d181721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192827, d181721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192828 q = 1) : d181722 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192828, d181722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192828, d181722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192829 q = 1) : d181723 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192829, d181723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192829, d181723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192830 q = 1) : d181724 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192830, d181724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192830, d181724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55837 (p : Pattern) (ha : d180908 p = 1) (hb : d192836 p = 1) : d181730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192831 q = 1) : d181725 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192831, d181725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192831, d181725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55836 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192832 q = 1) : d181726 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192832, d181726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192832, d181726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192833 q = 1) : d181727 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192833, d181727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192833, d181727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192834 q = 1) : d181728 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192834, d181728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192834, d181728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192835 q = 1) : d181729 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192835, d181729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192835, d181729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192836 q = 1) : d181730 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192836, d181730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192836, d181730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55838 (p : Pattern) (ha : d180908 p = 1) (hb : d192841 p = 1) : d181736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d180908 q = 1) : d181475 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55797 q ha hb
    | true =>
      simp only [d17397, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55787 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d180908 q = 1) : d181476 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d180908 q = 1) : d181477 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d180908 q = 1) : d181485 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55787 q ha hb
    | true =>
      simp only [d17400, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55795 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d180908 q = 1) : d181486 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d180908 q = 1) : d181487 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d180908 q = 1) : d181488 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17417 q = 1) (hb : d180908 q = 1) : d181506 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55787 q ha hb
    | true =>
      simp only [d17417, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55786 q ha hb
  have h9 (q : Pattern) (ha : d17418 q = 1) (hb : d180908 q = 1) : d181507 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17418, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17419 q = 1) (hb : d180908 q = 1) : d181508 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17420 q = 1) (hb : d180908 q = 1) : d181509 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17420, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171214 q = 1) (hb : d180908 q = 1) : d181735 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171214, d181735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171214, d181735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10398 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55792 q ha hb
    | true =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55784 q ha hb
  have h14 (q : Pattern) (ha : d10399 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10400 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10419 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55784 q ha hb
    | true =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55794 q ha hb
  have h17 (q : Pattern) (ha : d10420 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10421 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10422 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10441 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55784 q ha hb
    | true =>
      simp only [d10441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55785 q ha hb
  have h21 (q : Pattern) (ha : d10442 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10443 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10444 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d129598 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d129598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d180908 q = 1) (hb : d192841 q = 1) : d181736 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d192841, d181736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d192841, d181736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  exact h25 p ha hb
theorem andIntro55839 (p : Pattern) (ha : d180908 p = 1) (hb : d192847 p = 1) : d181742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192842 q = 1) : d181737 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d192842, d181737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55838 q ha hb
    | true =>
      simp only [d192842, d181737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192843 q = 1) : d181738 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d192843, d181738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192843, d181738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20785 q = 1) (hb : d180908 q = 1) : d181512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20785, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55788 q ha hb
    | true =>
      simp only [d20785, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20786 q = 1) (hb : d180908 q = 1) : d181513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20786, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20786, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192844 q = 1) : d181739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d192844, d181739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192844, d181739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192845 q = 1) : d181740 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d192845, d181740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192845, d181740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d180908 q = 1) (hb : d192846 q = 1) : d181741 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d192846, d181741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192846, d181741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d180908 q = 1) (hb : d192847 q = 1) : d181742 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d192847, d181742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192847, d181742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro55840 (p : Pattern) (ha : d180908 p = 1) (hb : d192853 p = 1) : d181748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192848 q = 1) : d181743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192848, d181743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55839 q ha hb
    | true =>
      simp only [d192848, d181743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55789 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192849 q = 1) : d181744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192849, d181744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192849, d181744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192850 q = 1) : d181745 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192850, d181745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192850, d181745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192851 q = 1) : d181746 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192851, d181746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192851, d181746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192852 q = 1) : d181747 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192852, d181747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192852, d181747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192853 q = 1) : d181748 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192853, d181748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192853, d181748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55841 (p : Pattern) (ha : d180908 p = 1) (hb : d192859 p = 1) : d181754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192854 q = 1) : d181749 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192854, d181749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192854, d181749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55840 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192855 q = 1) : d181750 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192855, d181750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192855, d181750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192856 q = 1) : d181751 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192856, d181751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192856, d181751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192857 q = 1) : d181752 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192857, d181752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192857, d181752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192858 q = 1) : d181753 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192858, d181753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192858, d181753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192859 q = 1) : d181754 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192859, d181754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192859, d181754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55842 (p : Pattern) (ha : d180908 p = 1) (hb : d192865 p = 1) : d181760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192860 q = 1) : d181755 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192860, d181755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192860, d181755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55841 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192861 q = 1) : d181756 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192861, d181756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192861, d181756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192862 q = 1) : d181757 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192862, d181757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192862, d181757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192863 q = 1) : d181758 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192863, d181758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192863, d181758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192864 q = 1) : d181759 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192864, d181759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192864, d181759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192865 q = 1) : d181760 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192865, d181760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192865, d181760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55843 (p : Pattern) (ha : d180908 p = 1) (hb : d192871 p = 1) : d181766 p = 1 := by
  have h0 (q : Pattern) (ha : d180908 q = 1) (hb : d192763 q = 1) : d181655 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192763, d181655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55821 q ha hb
    | true =>
      simp only [d192763, d181655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55824 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192782 q = 1) : d181674 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192782, d181674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192782, d181674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55827 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192783 q = 1) : d181675 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192783, d181675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192783, d181675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192809 q = 1) : d181702 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192809, d181702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192809, d181702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55832 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192810 q = 1) : d181703 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192810, d181703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192810, d181703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192811 q = 1) : d181704 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d192811, d181704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192811, d181704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d180908 q = 1) (hb : d192837 q = 1) : d181731 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192837, d181731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192837, d181731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55837 q ha hb
  have h8 (q : Pattern) (ha : d180908 q = 1) (hb : d192838 q = 1) : d181732 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192838, d181732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192838, d181732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d180908 q = 1) (hb : d192839 q = 1) : d181733 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d192839, d181733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192839, d181733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d180908 q = 1) (hb : d192840 q = 1) : d181734 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d192840, d181734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192840, d181734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d180908 q = 1) (hb : d192866 q = 1) : d181761 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192866, d181761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192866, d181761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55842 q ha hb
  have h12 (q : Pattern) (ha : d180908 q = 1) (hb : d192867 q = 1) : d181762 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192867, d181762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192867, d181762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d180908 q = 1) (hb : d192868 q = 1) : d181763 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d192868, d181763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192868, d181763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d180908 q = 1) (hb : d192869 q = 1) : d181764 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d192869, d181764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192869, d181764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d180908 q = 1) (hb : d192870 q = 1) : d181765 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d192870, d181765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d192870, d181765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d180908 q = 1) (hb : d192871 q = 1) : d181766 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d192871, d181766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d192871, d181766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro55844 (p : Pattern) (ha : d180908 p = 1) (hb : d192877 p = 1) : d181772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192872 q = 1) : d181767 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d192872, d181767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55843 q ha hb
    | true =>
      simp only [d192872, d181767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192873 q = 1) : d181768 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d192873, d181768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192873, d181768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192874 q = 1) : d181769 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d192874, d181769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192874, d181769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192875 q = 1) : d181770 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d192875, d181770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192875, d181770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192876 q = 1) : d181771 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d192876, d181771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192876, d181771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192877 q = 1) : d181772 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d192877, d181772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192877, d181772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55845 (p : Pattern) (ha : d180908 p = 1) (hb : d192883 p = 1) : d181778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192878 q = 1) : d181773 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d192878, d181773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55844 q ha hb
    | true =>
      simp only [d192878, d181773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192879 q = 1) : d181774 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d192879, d181774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192879, d181774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192880 q = 1) : d181775 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d192880, d181775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192880, d181775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192881 q = 1) : d181776 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d192881, d181776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192881, d181776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d192882 q = 1) : d181777 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d192882, d181777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192882, d181777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d192883 q = 1) : d181778 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d192883, d181778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192883, d181778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55846 (p : Pattern) (ha : d187676 p = 1) (hb : d192889 p = 1) : d181784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d192884 q = 1) : d181779 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d192884, d181779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55845 q ha hb
    | true =>
      simp only [d192884, d181779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d192885 q = 1) : d181780 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d192885, d181780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192885, d181780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d192886 q = 1) : d181781 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d192886, d181781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192886, d181781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d192887 q = 1) : d181782 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d192887, d181782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192887, d181782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d187676 q = 1) (hb : d192888 q = 1) : d181783 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d187676, d192888, d181783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187676, d192888, d181783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d187676 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d187676 q = 1) (hb : d192889 q = 1) : d181784 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d192889, d181784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192889, d181784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro55847 (p : Pattern) (ha : d187676 p = 1) (hb : d192895 p = 1) : d181790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d187676 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d187676 q = 1) (hb : d192890 q = 1) : d181785 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d192890, d181785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55846 q ha hb
    | true =>
      simp only [d192890, d181785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d187676 q = 1) (hb : d192891 q = 1) : d181786 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d192891, d181786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192891, d181786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d187676 q = 1) (hb : d192892 q = 1) : d181787 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d192892, d181787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192892, d181787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d187676 q = 1) (hb : d192893 q = 1) : d181788 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d192893, d181788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192893, d181788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d187676 q = 1) (hb : d192894 q = 1) : d181789 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d192894, d181789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192894, d181789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d187676 q = 1) (hb : d192895 q = 1) : d181790 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d192895, d181790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192895, d181790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55848 (p : Pattern) (ha : d187676 p = 1) (hb : d192901 p = 1) : d181796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d187676 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d187676 q = 1) (hb : d192896 q = 1) : d181791 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d192896, d181791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55847 q ha hb
    | true =>
      simp only [d192896, d181791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d187676 q = 1) (hb : d192897 q = 1) : d181792 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d192897, d181792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192897, d181792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d187676 q = 1) (hb : d192898 q = 1) : d181793 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d192898, d181793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192898, d181793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d187676 q = 1) (hb : d192899 q = 1) : d181794 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d192899, d181794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192899, d181794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d187676 q = 1) (hb : d192900 q = 1) : d181795 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d192900, d181795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192900, d181795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d187676 q = 1) (hb : d192901 q = 1) : d181796 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d192901, d181796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192901, d181796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55849 (p : Pattern) (ha : d187676 p = 1) (hb : d192907 p = 1) : d181802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d187676 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d187676 q = 1) (hb : d192902 q = 1) : d181797 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d192902, d181797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55848 q ha hb
    | true =>
      simp only [d192902, d181797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d187676 q = 1) (hb : d192903 q = 1) : d181798 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d192903, d181798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192903, d181798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d187676 q = 1) (hb : d192904 q = 1) : d181799 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d192904, d181799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192904, d181799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d187676 q = 1) (hb : d192905 q = 1) : d181800 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d192905, d181800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192905, d181800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d187676 q = 1) (hb : d192906 q = 1) : d181801 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d192906, d181801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192906, d181801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d187676 q = 1) (hb : d192907 q = 1) : d181802 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d192907, d181802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192907, d181802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55850 (p : Pattern) (ha : d187676 p = 1) (hb : d192913 p = 1) : d181808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d187676 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d187676 q = 1) (hb : d192908 q = 1) : d181803 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d192908, d181803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55849 q ha hb
    | true =>
      simp only [d192908, d181803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d187676 q = 1) (hb : d192909 q = 1) : d181804 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d192909, d181804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192909, d181804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d187676 q = 1) (hb : d192910 q = 1) : d181805 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d192910, d181805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192910, d181805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d187676 q = 1) (hb : d192911 q = 1) : d181806 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d192911, d181806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192911, d181806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d187676 q = 1) (hb : d192912 q = 1) : d181807 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d192912, d181807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192912, d181807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d187676 q = 1) (hb : d192913 q = 1) : d181808 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d192913, d181808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192913, d181808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55851 (p : Pattern) (ha : d131071 p = 1) (hb : d190593 p = 1) : d130362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d131066 q = 1) : d130357 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d131066, d130357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45072 q ha hb
    | true =>
      simp only [d131066, d130357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d131067 q = 1) : d130358 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d131067, d130358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131067, d130358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d131068 q = 1) : d130359 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d131068, d130359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131068, d130359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131069 q = 1) (hb : d190593 q = 1) : d130360 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d131069, d190593, d130360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d131069, d190593, d130360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d190593 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d131070 q = 1) (hb : d190593 q = 1) : d130361 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d131070, d130361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131070, d130361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131071 q = 1) (hb : d190593 q = 1) : d130362 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d131071, d130362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131071, d130362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro55852 (p : Pattern) (ha : d131077 p = 1) (hb : d190593 p = 1) : d130368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d190593 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131072 q = 1) (hb : d190593 q = 1) : d130363 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d131072, d130363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55851 q ha hb
    | true =>
      simp only [d131072, d130363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131073 q = 1) (hb : d190593 q = 1) : d130364 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d131073, d130364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131073, d130364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131074 q = 1) (hb : d190593 q = 1) : d130365 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d131074, d130365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131074, d130365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131075 q = 1) (hb : d190593 q = 1) : d130366 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d131075, d130366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131075, d130366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131076 q = 1) (hb : d190593 q = 1) : d130367 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d131076, d130367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131076, d130367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131077 q = 1) (hb : d190593 q = 1) : d130368 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d131077, d130368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131077, d130368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55853 (p : Pattern) (ha : d131083 p = 1) (hb : d190593 p = 1) : d130374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d190593 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131078 q = 1) (hb : d190593 q = 1) : d130369 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d131078, d130369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55852 q ha hb
    | true =>
      simp only [d131078, d130369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131079 q = 1) (hb : d190593 q = 1) : d130370 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d131079, d130370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131079, d130370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131080 q = 1) (hb : d190593 q = 1) : d130371 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d131080, d130371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131080, d130371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131081 q = 1) (hb : d190593 q = 1) : d130372 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d131081, d130372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131081, d130372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131082 q = 1) (hb : d190593 q = 1) : d130373 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d131082, d130373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131082, d130373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131083 q = 1) (hb : d190593 q = 1) : d130374 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d131083, d130374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131083, d130374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55854 (p : Pattern) (ha : d131089 p = 1) (hb : d190593 p = 1) : d130380 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d190593 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131084 q = 1) (hb : d190593 q = 1) : d130375 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d131084, d130375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55853 q ha hb
    | true =>
      simp only [d131084, d130375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131085 q = 1) (hb : d190593 q = 1) : d130376 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d131085, d130376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131085, d130376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131086 q = 1) (hb : d190593 q = 1) : d130377 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d131086, d130377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131086, d130377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131087 q = 1) (hb : d190593 q = 1) : d130378 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d131087, d130378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131087, d130378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131088 q = 1) (hb : d190593 q = 1) : d130379 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d131088, d130379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131088, d130379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131089 q = 1) (hb : d190593 q = 1) : d130380 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d131089, d130380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131089, d130380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55855 (p : Pattern) (ha : d131095 p = 1) (hb : d190593 p = 1) : d130386 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d190593 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131090 q = 1) (hb : d190593 q = 1) : d130381 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d131090, d130381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55854 q ha hb
    | true =>
      simp only [d131090, d130381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131091 q = 1) (hb : d190593 q = 1) : d130382 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d131091, d130382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131091, d130382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131092 q = 1) (hb : d190593 q = 1) : d130383 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d131092, d130383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131092, d130383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131093 q = 1) (hb : d190593 q = 1) : d130384 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d131093, d130384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131093, d130384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131094 q = 1) (hb : d190593 q = 1) : d130385 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d131094, d130385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131094, d130385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131095 q = 1) (hb : d190593 q = 1) : d130386 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d131095, d130386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131095, d130386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55856 (p : Pattern) (ha : d190593 p = 1) (hb : d192889 p = 1) : d188699 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192884 q = 1) : d188694 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d192884, d188694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45186 q ha hb
    | true =>
      simp only [d192884, d188694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192885 q = 1) : d188695 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d192885, d188695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192885, d188695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192886 q = 1) : d188696 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d192886, d188696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192886, d188696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d190593 q = 1) (hb : d192887 q = 1) : d188697 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d190593, d192887, d188697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190593, d192887, d188697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d190593 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d190593 q = 1) (hb : d192888 q = 1) : d188698 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d192888, d188698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192888, d188698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d190593 q = 1) (hb : d192889 q = 1) : d188699 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d192889, d188699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192889, d188699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h8 p ha hb
theorem andIntro55857 (p : Pattern) (ha : d190593 p = 1) (hb : d192895 p = 1) : d188705 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d190593 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190593 q = 1) (hb : d192890 q = 1) : d188700 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d192890, d188700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55856 q ha hb
    | true =>
      simp only [d192890, d188700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d190593 q = 1) (hb : d192891 q = 1) : d188701 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d192891, d188701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192891, d188701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d190593 q = 1) (hb : d192892 q = 1) : d188702 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d192892, d188702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192892, d188702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d190593 q = 1) (hb : d192893 q = 1) : d188703 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d192893, d188703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192893, d188703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d190593 q = 1) (hb : d192894 q = 1) : d188704 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d192894, d188704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192894, d188704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d190593 q = 1) (hb : d192895 q = 1) : d188705 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d192895, d188705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192895, d188705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55858 (p : Pattern) (ha : d190593 p = 1) (hb : d192901 p = 1) : d188711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d190593 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190593 q = 1) (hb : d192896 q = 1) : d188706 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d192896, d188706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55857 q ha hb
    | true =>
      simp only [d192896, d188706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d190593 q = 1) (hb : d192897 q = 1) : d188707 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d192897, d188707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192897, d188707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d190593 q = 1) (hb : d192898 q = 1) : d188708 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d192898, d188708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192898, d188708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d190593 q = 1) (hb : d192899 q = 1) : d188709 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d192899, d188709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192899, d188709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d190593 q = 1) (hb : d192900 q = 1) : d188710 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d192900, d188710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192900, d188710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d190593 q = 1) (hb : d192901 q = 1) : d188711 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d192901, d188711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192901, d188711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55859 (p : Pattern) (ha : d190593 p = 1) (hb : d192907 p = 1) : d188717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d190593 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190593 q = 1) (hb : d192902 q = 1) : d188712 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d192902, d188712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55858 q ha hb
    | true =>
      simp only [d192902, d188712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d190593 q = 1) (hb : d192903 q = 1) : d188713 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d192903, d188713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192903, d188713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d190593 q = 1) (hb : d192904 q = 1) : d188714 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d192904, d188714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192904, d188714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d190593 q = 1) (hb : d192905 q = 1) : d188715 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d192905, d188715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192905, d188715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d190593 q = 1) (hb : d192906 q = 1) : d188716 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d192906, d188716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192906, d188716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d190593 q = 1) (hb : d192907 q = 1) : d188717 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d192907, d188717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192907, d188717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55860 (p : Pattern) (ha : d190593 p = 1) (hb : d192913 p = 1) : d188723 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d190593 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190593 q = 1) (hb : d192908 q = 1) : d188718 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d192908, d188718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55859 q ha hb
    | true =>
      simp only [d192908, d188718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d190593 q = 1) (hb : d192909 q = 1) : d188719 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d192909, d188719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192909, d188719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d190593 q = 1) (hb : d192910 q = 1) : d188720 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d192910, d188720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192910, d188720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d190593 q = 1) (hb : d192911 q = 1) : d188721 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d192911, d188721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192911, d188721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d190593 q = 1) (hb : d192912 q = 1) : d188722 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d192912, d188722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192912, d188722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d190593 q = 1) (hb : d192913 q = 1) : d188723 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d192913, d188723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192913, d188723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55861 (p : Pattern) (ha : d20390 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d72 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d73 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d73, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d74 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9297 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23454 q ha hb
    | true =>
      simp only [d9297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9298 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9298, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9299 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9300 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9301 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d20390 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro55862 (p : Pattern) (ha : d20396 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20391 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55861 q ha hb
    | true =>
      simp only [d20391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20392 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20393 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20394 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20395 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20396 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55863 (p : Pattern) (ha : d20402 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20397 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55862 q ha hb
    | true =>
      simp only [d20397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20398 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20399 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20400 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20401 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20402 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55864 (p : Pattern) (ha : d20408 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20403 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55863 q ha hb
  have h2 (q : Pattern) (ha : d20404 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20405 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20406 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20407 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20408 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55865 (p : Pattern) (ha : d20413 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d232 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d233, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d72 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d73 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d73, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d235 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d236 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9330 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23459 q ha hb
    | true =>
      simp only [d9330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23454 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9331 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9331, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9332 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9297 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23454 q ha hb
    | true =>
      simp only [d9297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d9298 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9298, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h17 (q : Pattern) (ha : d9299 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9333 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9300 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d9334 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d20413 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro55866 (p : Pattern) (ha : d20419 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20414 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55865 q ha hb
    | true =>
      simp only [d20414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20415 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20391 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55861 q ha hb
    | true =>
      simp only [d20391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20392 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20416 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20417 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20418 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20419 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55867 (p : Pattern) (ha : d130389 p = 1) (hb : d130924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20420 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55866 q ha hb
    | true =>
      simp only [d20420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55862 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d130920 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20397 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55862 q ha hb
    | true =>
      simp only [d20397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20398 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d130921 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d130922 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130389 q = 1) (hb : d130923 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130389 q = 1) (hb : d130924 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55868 (p : Pattern) (ha : d130389 p = 1) (hb : d130930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d130925 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55867 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d130926 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d130927 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d130928 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d130929 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d130930 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55869 (p : Pattern) (ha : d20477 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20397 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55862 q ha hb
    | true =>
      simp only [d20397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20473 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20474 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20475 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20476 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20477 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55870 (p : Pattern) (ha : d20445 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16005 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16006 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16006, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d16007 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d232 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d233, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d72 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d73 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d73, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d74 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d235 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16009 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9389 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23465 q ha hb
    | true =>
      simp only [d9389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23459 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d9390 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9390, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9391 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9330 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23459 q ha hb
    | true =>
      simp only [d9330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23454 q ha hb
  have h19 (q : Pattern) (ha : d9331 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9331, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h20 (q : Pattern) (ha : d9332 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9392 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d9297 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23454 q ha hb
    | true =>
      simp only [d9297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h23 (q : Pattern) (ha : d9298 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9298, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h24 (q : Pattern) (ha : d9299 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d9333 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d9393 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d20445 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro55871 (p : Pattern) (ha : d20451 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20446 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55870 q ha hb
    | true =>
      simp only [d20446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20447 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20414 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55865 q ha hb
    | true =>
      simp only [d20414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20415 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20448 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20449 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20450 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20451 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55872 (p : Pattern) (ha : d20465 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20414 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55865 q ha hb
    | true =>
      simp only [d20414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20415 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20462 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20463 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20464 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20465 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55873 (p : Pattern) (ha : d130389 p = 1) (hb : d130940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20452 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55871 q ha hb
    | true =>
      simp only [d20452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55866 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d130936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20466 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55872 q ha hb
    | true =>
      simp only [d20466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20467 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d130937 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d130938 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130389 q = 1) (hb : d130939 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130389 q = 1) (hb : d130940 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55874 (p : Pattern) (ha : d130389 p = 1) (hb : d130946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d130941 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55873 q ha hb
  have h2 (q : Pattern) (ha : d20478 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55869 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d130942 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d130943 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d130944 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d130945 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130389 q = 1) (hb : d130946 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro55875 (p : Pattern) (ha : d130389 p = 1) (hb : d130952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20409 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55864 q ha hb
  have h2 (q : Pattern) (ha : d20410 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20411 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20412 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d130931 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55868 q ha hb
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d130932 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130389 q = 1) (hb : d130933 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130389 q = 1) (hb : d130934 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130389 q = 1) (hb : d130935 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d130935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130389 q = 1) (hb : d130947 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55874 q ha hb
  have h11 (q : Pattern) (ha : d130389 q = 1) (hb : d130948 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d130389 q = 1) (hb : d130949 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d130389 q = 1) (hb : d130950 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d130389 q = 1) (hb : d130951 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d130389 q = 1) (hb : d130952 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d130952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro55876 (p : Pattern) (ha : d20500 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d232 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d233, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d673 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d682 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9330 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23459 q ha hb
    | true =>
      simp only [d9330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23454 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9331 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9331, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9332 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9487 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9496 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d20500 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro55877 (p : Pattern) (ha : d20538 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20501 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55876 q ha hb
    | true =>
      simp only [d20501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20502 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20535 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20536 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20537 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20538 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55878 (p : Pattern) (ha : d20544 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20539 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55877 q ha hb
    | true =>
      simp only [d20539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20540 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20541 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20542 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20543 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20544 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55879 (p : Pattern) (ha : d20490 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16163 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16164 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16164, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16164, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d16165 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16167 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d16168 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16168, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16168, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d16169 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16170 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16005 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16006 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16006, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d16007 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d232 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d233 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d233, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d234 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16008 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16171 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9475 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23475 q ha hb
    | true =>
      simp only [d9475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23465 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d9476 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9476, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9476, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9477 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9479 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23465 q ha hb
    | true =>
      simp only [d9479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23476 q ha hb
  have h22 (q : Pattern) (ha : d9480 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9480, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9480, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h23 (q : Pattern) (ha : d9481 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d9482 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d9389 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23465 q ha hb
    | true =>
      simp only [d9389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23459 q ha hb
  have h26 (q : Pattern) (ha : d9390 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d9390, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h27 (q : Pattern) (ha : d9391 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d9330 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23459 q ha hb
    | true =>
      simp only [d9330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23454 q ha hb
  have h29 (q : Pattern) (ha : d9331 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d9331, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h30 (q : Pattern) (ha : d9332 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d9392 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d9392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d9483 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d9483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d20490 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d20490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro55880 (p : Pattern) (ha : d20493 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16005 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16006 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16006, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d16007 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d232 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d233, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d673 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16175 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9389 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23465 q ha hb
    | true =>
      simp only [d9389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23459 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9390 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9390, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9391 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9330 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23459 q ha hb
    | true =>
      simp only [d9330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23454 q ha hb
  have h16 (q : Pattern) (ha : d9331 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9331, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h17 (q : Pattern) (ha : d9332 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9392 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9487 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d9488 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d20493 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro55881 (p : Pattern) (ha : d20499 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20491 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55879 q ha hb
    | true =>
      simp only [d20491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20492 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20494 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55880 q ha hb
    | true =>
      simp only [d20494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20495 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20496 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20497 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20498 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20499 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55882 (p : Pattern) (ha : d20506 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20494 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55880 q ha hb
    | true =>
      simp only [d20494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20495 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20501 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55876 q ha hb
    | true =>
      simp only [d20501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20502 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20503 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20504 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20505 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20506 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55883 (p : Pattern) (ha : d20527 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20494 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55880 q ha hb
    | true =>
      simp only [d20494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20495 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20524 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20525 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20526 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20527 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55884 (p : Pattern) (ha : d130389 p = 1) (hb : d130957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20507 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55881 q ha hb
    | true =>
      simp only [d20507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55882 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d130953 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20528 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55883 q ha hb
    | true =>
      simp only [d20528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20529 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d130954 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d130955 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130389 q = 1) (hb : d130956 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130389 q = 1) (hb : d130957 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55885 (p : Pattern) (ha : d130389 p = 1) (hb : d130963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d130958 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55884 q ha hb
  have h2 (q : Pattern) (ha : d20545 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55878 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d130959 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d130960 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d130961 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d130962 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130389 q = 1) (hb : d130963 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro55886 (p : Pattern) (ha : d130389 p = 1) (hb : d130969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d130964 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55885 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d130965 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d130966 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d130967 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d130968 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d130969 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55887 (p : Pattern) (ha : d20568 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d987 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d988 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d988, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d989 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d995 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1004 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9624 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23485 q ha hb
    | true =>
      simp only [d9624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23486 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9625 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9625, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9626 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9632 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9641 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d20568 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro55888 (p : Pattern) (ha : d20606 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20569 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55887 q ha hb
    | true =>
      simp only [d20569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20570 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20603 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20604 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20605 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20606 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55889 (p : Pattern) (ha : d20612 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20607 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55888 q ha hb
    | true =>
      simp only [d20607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20608 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20609 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20610 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20611 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20612 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55890 (p : Pattern) (ha : d20558 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16364 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16365 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16365, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16365, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d16366 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16368 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d16369 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16369, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16369, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d16370 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16371 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16372 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16373 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16373, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d16374 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d987 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d988 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d988, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d989 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16375 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16376 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9609 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23490 q ha hb
    | true =>
      simp only [d9609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23491 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d9610 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9610, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9610, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9611 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9614 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23491 q ha hb
    | true =>
      simp only [d9614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23492 q ha hb
  have h22 (q : Pattern) (ha : d9615 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9615, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9615, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h23 (q : Pattern) (ha : d9616 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d9617 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d9620 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23491 q ha hb
    | true =>
      simp only [d9620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23485 q ha hb
  have h26 (q : Pattern) (ha : d9621 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9621, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d9621, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h27 (q : Pattern) (ha : d9622 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d9624 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23485 q ha hb
    | true =>
      simp only [d9624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23486 q ha hb
  have h29 (q : Pattern) (ha : d9625 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d9625, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h30 (q : Pattern) (ha : d9626 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d9627 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d9627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d9628 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d9628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d20558 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d20558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro55891 (p : Pattern) (ha : d20561 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16372 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16373 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16373, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d16374 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d987 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d988 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d988, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d989 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16375 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d995 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16380 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9620 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23491 q ha hb
    | true =>
      simp only [d9620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23485 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9621 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9621, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9621, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9622 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9624 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23485 q ha hb
    | true =>
      simp only [d9624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23486 q ha hb
  have h16 (q : Pattern) (ha : d9625 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9625, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h17 (q : Pattern) (ha : d9626 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9627 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9632 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d9633 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d20561 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro55892 (p : Pattern) (ha : d20567 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20559 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55890 q ha hb
    | true =>
      simp only [d20559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20560 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20562 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55891 q ha hb
    | true =>
      simp only [d20562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20563 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20564 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20565 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20566 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20567 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55893 (p : Pattern) (ha : d20574 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20562 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55891 q ha hb
    | true =>
      simp only [d20562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20563 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20569 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55887 q ha hb
    | true =>
      simp only [d20569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20570 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20571 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20572 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20573 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20574 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55894 (p : Pattern) (ha : d20595 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20562 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55891 q ha hb
    | true =>
      simp only [d20562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20563 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20592 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20593 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20594 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20595 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55895 (p : Pattern) (ha : d130389 p = 1) (hb : d130975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20575 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55892 q ha hb
    | true =>
      simp only [d20575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55893 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d130971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20596 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55894 q ha hb
    | true =>
      simp only [d20596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20597 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d130972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d130973 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130389 q = 1) (hb : d130974 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130389 q = 1) (hb : d130975 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55896 (p : Pattern) (ha : d130389 p = 1) (hb : d130981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d130976 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55895 q ha hb
  have h2 (q : Pattern) (ha : d20613 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55889 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d130977 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d130978 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d130979 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d130980 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130389 q = 1) (hb : d130981 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro55897 (p : Pattern) (ha : d130389 p = 1) (hb : d130987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d130982 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55896 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d130983 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d130984 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d130985 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d130986 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d130987 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55898 (p : Pattern) (ha : d20637 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16693 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16694 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16694, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d16695 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16696 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16697 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9870 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
    | true =>
      simp only [d9870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23502 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9871 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9871, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9871, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9872 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9873 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9874 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d20637 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro55899 (p : Pattern) (ha : d20678 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20638 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55898 q ha hb
    | true =>
      simp only [d20638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20639 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20675 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20676 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20677 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20678 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55900 (p : Pattern) (ha : d20684 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20679 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55899 q ha hb
    | true =>
      simp only [d20679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20680 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20681 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20682 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20683 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20684 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55901 (p : Pattern) (ha : d20627 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16663 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16664 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16664, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16664, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d16665 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16668 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d16669 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16669, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16669, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d16670 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16671 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16673 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16674 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16674, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d16675 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d16676 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d16677 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16677, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d16678 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16679 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16680 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9807 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23506 q ha hb
    | true =>
      simp only [d9807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23507 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d9808 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9808, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9808, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9809 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9822 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23507 q ha hb
    | true =>
      simp only [d9822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23508 q ha hb
  have h22 (q : Pattern) (ha : d9823 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9823, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9823, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h23 (q : Pattern) (ha : d9824 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d9825 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d9834 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23507 q ha hb
    | true =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
  have h26 (q : Pattern) (ha : d9835 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d9835, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h27 (q : Pattern) (ha : d9836 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d9851 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
    | true =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23509 q ha hb
  have h29 (q : Pattern) (ha : d9852 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d9852, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h30 (q : Pattern) (ha : d9853 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d9854 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d9855 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d9855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d20627 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d20627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro55902 (p : Pattern) (ha : d20630 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16673 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16674 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16674, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d16675 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16676 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d16677 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16677, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d16678 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16679 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d16684 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16685 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9834 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23507 q ha hb
    | true =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9835 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9835, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9836 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9851 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
    | true =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23509 q ha hb
  have h16 (q : Pattern) (ha : d9852 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9852, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h17 (q : Pattern) (ha : d9853 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9854 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9859 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d9860 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d20630 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro55903 (p : Pattern) (ha : d20636 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20628 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55901 q ha hb
    | true =>
      simp only [d20628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20629 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20631 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55902 q ha hb
    | true =>
      simp only [d20631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20632 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20633 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20634 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20635 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20636 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55904 (p : Pattern) (ha : d20643 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20631 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55902 q ha hb
    | true =>
      simp only [d20631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20632 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20638 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55898 q ha hb
    | true =>
      simp only [d20638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20639 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20640 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20641 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20642 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20643 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55905 (p : Pattern) (ha : d20661 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16673 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16674 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16674, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d16675 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16676 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d16677 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16677, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d16678 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16679 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16743 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16744 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16744, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16744, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d16745 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16746 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16747 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9834 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23507 q ha hb
    | true =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d9835 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9835, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9836 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9851 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
    | true =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23509 q ha hb
  have h19 (q : Pattern) (ha : d9852 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9852, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h20 (q : Pattern) (ha : d9853 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9854 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d9988 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
    | true =>
      simp only [d9988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23514 q ha hb
  have h23 (q : Pattern) (ha : d9989 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9989, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9989, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h24 (q : Pattern) (ha : d9990 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d9991 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d9991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d9992 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d20661 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro55906 (p : Pattern) (ha : d20667 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20662 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55905 q ha hb
    | true =>
      simp only [d20662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20663 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20664 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20665 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20666 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20667 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55907 (p : Pattern) (ha : d130389 p = 1) (hb : d130994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20644 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55903 q ha hb
    | true =>
      simp only [d20644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55904 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d130990 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20668 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55906 q ha hb
    | true =>
      simp only [d20668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20669 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d130991 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d130992 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130389 q = 1) (hb : d130993 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130389 q = 1) (hb : d130994 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55908 (p : Pattern) (ha : d130389 p = 1) (hb : d131000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d130995 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55907 q ha hb
  have h2 (q : Pattern) (ha : d20685 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55900 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d130996 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d130997 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d130998 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d130999 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130389 q = 1) (hb : d131000 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro55909 (p : Pattern) (ha : d130389 p = 1) (hb : d131006 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d131001 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55908 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d131002 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d131003 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d131004 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d131005 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d131006 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55910 (p : Pattern) (ha : d20710 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17053 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17054 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17054, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17055 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17056 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17057 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10164 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
    | true =>
      simp only [d10164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23521 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10165 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10165, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10165, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10166 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10167 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10168 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d20710 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro55911 (p : Pattern) (ha : d20751 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20711 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55910 q ha hb
    | true =>
      simp only [d20711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20712 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20748 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20749 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20750 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20751 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55912 (p : Pattern) (ha : d20757 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20752 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55911 q ha hb
    | true =>
      simp only [d20752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20753 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20754 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20755 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20756 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20757 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55913 (p : Pattern) (ha : d20700 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17018 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17019 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17019, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17019, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17020 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17023 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17024 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17024, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17024, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d17025 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17026 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d17033 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17034 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17034, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d17035 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d17036 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d17037 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17037, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d17038 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17039 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17040 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10092 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23525 q ha hb
    | true =>
      simp only [d10092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23526 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d10093 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10093, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10093, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10094 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10107 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23526 q ha hb
    | true =>
      simp only [d10107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23527 q ha hb
  have h22 (q : Pattern) (ha : d10108 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10108, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d10108, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h23 (q : Pattern) (ha : d10109 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d10110 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d10122 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23526 q ha hb
    | true =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
  have h26 (q : Pattern) (ha : d10123 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d10123, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h27 (q : Pattern) (ha : d10124 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d10142 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
    | true =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23528 q ha hb
  have h29 (q : Pattern) (ha : d10143 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d10143, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h30 (q : Pattern) (ha : d10144 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d10145 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d10146 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d10146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d20700 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d20700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro55914 (p : Pattern) (ha : d20703 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17033 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17034 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17034, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17035 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17036 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17037 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17037, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d17038 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17039 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17044 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17045 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10122 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23526 q ha hb
    | true =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d10123 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10123, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10124 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10142 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
    | true =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23528 q ha hb
  have h16 (q : Pattern) (ha : d10143 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10143, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h17 (q : Pattern) (ha : d10144 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10145 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10150 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d10151 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d20703 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro55915 (p : Pattern) (ha : d20709 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20701 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55913 q ha hb
    | true =>
      simp only [d20701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20702 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20704 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55914 q ha hb
    | true =>
      simp only [d20704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20705 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20706 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20707 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20708 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20709 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55916 (p : Pattern) (ha : d20716 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20704 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55914 q ha hb
    | true =>
      simp only [d20704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20705 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20711 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55910 q ha hb
    | true =>
      simp only [d20711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20712 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20713 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20714 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20715 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20716 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55917 (p : Pattern) (ha : d20734 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17033 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17034 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17034, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17035 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17036 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17037 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17037, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d17038 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17039 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d17108 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17109 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17109, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17109, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d17110 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17111 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17112 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10122 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23526 q ha hb
    | true =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10123 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10123, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10124 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10142 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
    | true =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23528 q ha hb
  have h19 (q : Pattern) (ha : d10143 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10143, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h20 (q : Pattern) (ha : d10144 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10145 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d10294 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
    | true =>
      simp only [d10294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23533 q ha hb
  have h23 (q : Pattern) (ha : d10295 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10295, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10295, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h24 (q : Pattern) (ha : d10296 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d10297 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d10297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d10298 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d10298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d20734 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro55918 (p : Pattern) (ha : d20740 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20735 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55917 q ha hb
    | true =>
      simp only [d20735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20736 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20737 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20738 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20739 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20740 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55919 (p : Pattern) (ha : d130389 p = 1) (hb : d131014 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20717 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55915 q ha hb
    | true =>
      simp only [d20717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55916 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d131010 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20741 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55918 q ha hb
    | true =>
      simp only [d20741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20742 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d131011 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d131012 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130389 q = 1) (hb : d131013 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130389 q = 1) (hb : d131014 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55920 (p : Pattern) (ha : d130389 p = 1) (hb : d131020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d131015 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55919 q ha hb
  have h2 (q : Pattern) (ha : d20758 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55912 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d131016 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d131017 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d131018 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d131019 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130389 q = 1) (hb : d131020 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro55921 (p : Pattern) (ha : d130389 p = 1) (hb : d131026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d131021 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55920 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d131022 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d131023 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d131024 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d131025 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d131026 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55922 (p : Pattern) (ha : d20784 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17417 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17418 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17418, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17419 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17420 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17421 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10441 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
    | true =>
      simp only [d10441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23540 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10442 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10442, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10442, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10443 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10444 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10445 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d20784 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro55923 (p : Pattern) (ha : d20825 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20785 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55922 q ha hb
    | true =>
      simp only [d20785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20786 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20822 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20823 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20824 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20825 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55924 (p : Pattern) (ha : d20831 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20826 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55923 q ha hb
    | true =>
      simp only [d20826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20827 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20828 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20829 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20830 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20831 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55925 (p : Pattern) (ha : d20774 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17383 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17384 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17384, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17384, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17385 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17387 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17388 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17388, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17388, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d17389 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17390 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d17397 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17398 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17398, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d17399 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d17400 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d17401 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17401, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d17402 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17403 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17404 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10378 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23544 q ha hb
    | true =>
      simp only [d10378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23545 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d10379 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10379, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10379, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10380 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10383 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23545 q ha hb
    | true =>
      simp only [d10383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23546 q ha hb
  have h22 (q : Pattern) (ha : d10384 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10384, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d10384, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h23 (q : Pattern) (ha : d10385 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d10386 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d10398 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23545 q ha hb
    | true =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
  have h26 (q : Pattern) (ha : d10399 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d10399, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h27 (q : Pattern) (ha : d10400 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d10419 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
    | true =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23547 q ha hb
  have h29 (q : Pattern) (ha : d10420 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d10420, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h30 (q : Pattern) (ha : d10421 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d10422 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d10423 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d10423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d20774 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d20774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro55926 (p : Pattern) (ha : d20777 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17397 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17398 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17398, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17399 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17400 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17401 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17401, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d17402 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17403 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17408 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17409 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10398 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23545 q ha hb
    | true =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d10399 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10399, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10400 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10419 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
    | true =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23547 q ha hb
  have h16 (q : Pattern) (ha : d10420 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10420, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h17 (q : Pattern) (ha : d10421 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10422 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10427 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d10428 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d20777 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro55927 (p : Pattern) (ha : d20783 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20775 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55925 q ha hb
    | true =>
      simp only [d20775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20776 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20778 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55926 q ha hb
    | true =>
      simp only [d20778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20779 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20780 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20781 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20782 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20783 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55928 (p : Pattern) (ha : d20790 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20778 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55926 q ha hb
    | true =>
      simp only [d20778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20779 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20785 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55922 q ha hb
    | true =>
      simp only [d20785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20786 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20787 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20788 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20789 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20790 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro55929 (p : Pattern) (ha : d20808 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17397 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17398 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17398, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17399 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17400 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17401 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17401, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d17402 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17403 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d17472 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17473 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17473, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17473, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d17474 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17475 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17476 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10398 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23545 q ha hb
    | true =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10399 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10399, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10400 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10419 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
    | true =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23547 q ha hb
  have h19 (q : Pattern) (ha : d10420 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10420, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h20 (q : Pattern) (ha : d10421 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10422 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d10560 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
    | true =>
      simp only [d10560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23552 q ha hb
  have h23 (q : Pattern) (ha : d10561 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10561, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10561, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h24 (q : Pattern) (ha : d10562 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d10563 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d10563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d10564 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d10564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d20808 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro55930 (p : Pattern) (ha : d20814 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20809 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55929 q ha hb
    | true =>
      simp only [d20809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20810 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20811 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20812 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20813 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20814 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55931 (p : Pattern) (ha : d130389 p = 1) (hb : d131035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20791 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55927 q ha hb
    | true =>
      simp only [d20791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55928 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d131031 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20815 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55930 q ha hb
    | true =>
      simp only [d20815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20816 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d131032 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d131033 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130389 q = 1) (hb : d131034 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130389 q = 1) (hb : d131035 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro55932 (p : Pattern) (ha : d130389 p = 1) (hb : d131041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d131036 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55931 q ha hb
  have h2 (q : Pattern) (ha : d20832 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55924 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d131037 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d131038 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d131039 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d131040 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130389 q = 1) (hb : d131041 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro55933 (p : Pattern) (ha : d130389 p = 1) (hb : d131047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d131042 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55932 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d131043 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d131044 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d131045 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d131046 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d131047 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55934 (p : Pattern) (ha : d130389 p = 1) (hb : d131053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d130389 q = 1) (hb : d130970 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55875 q ha hb
    | true =>
      simp only [d130970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55886 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d130988 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55897 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d130989 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d131007 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55909 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d131008 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d131009 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130389 q = 1) (hb : d131027 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55921 q ha hb
  have h8 (q : Pattern) (ha : d130389 q = 1) (hb : d131028 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130389 q = 1) (hb : d131029 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130389 q = 1) (hb : d131030 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d130389 q = 1) (hb : d131048 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55933 q ha hb
  have h12 (q : Pattern) (ha : d130389 q = 1) (hb : d131049 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d130389 q = 1) (hb : d131050 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d130389 q = 1) (hb : d131051 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d130389 q = 1) (hb : d131052 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d131052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d130389 q = 1) (hb : d131053 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d131053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro55935 (p : Pattern) (ha : d130389 p = 1) (hb : d131059 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d131054 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d131054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55934 q ha hb
    | true =>
      simp only [d131054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d131055 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d131055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d131056 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d131056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d131057 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d131057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d131058 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d131058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d131059 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d131059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55936 (p : Pattern) (ha : d130389 p = 1) (hb : d131065 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d131060 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d131060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55935 q ha hb
    | true =>
      simp only [d131060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d131061 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d131061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d131062 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d131062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d131063 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d131063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d131064 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d131064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d131065 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d131065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55937 (p : Pattern) (ha : d130390 p = 1) (hb : d131071 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d131066 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d131066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55936 q ha hb
    | true =>
      simp only [d131066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d131067 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d131067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d131068 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d131068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130390 q = 1) (hb : d131069 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d130390, d131069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130390, d131069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d130390 q = 1) (hb : d131070 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d131070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d130390 q = 1) (hb : d131071 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d131071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h8 p ha hb
theorem andIntro55938 (p : Pattern) (ha : d130390 p = 1) (hb : d131077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130390 q = 1) (hb : d131072 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d131072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55937 q ha hb
    | true =>
      simp only [d131072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130390 q = 1) (hb : d131073 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d131073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130390 q = 1) (hb : d131074 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d131074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130390 q = 1) (hb : d131075 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d131075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130390 q = 1) (hb : d131076 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d131076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130390 q = 1) (hb : d131077 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d131077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55939 (p : Pattern) (ha : d130390 p = 1) (hb : d131083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130390 q = 1) (hb : d131078 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d131078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55938 q ha hb
    | true =>
      simp only [d131078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130390 q = 1) (hb : d131079 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d131079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130390 q = 1) (hb : d131080 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d131080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130390 q = 1) (hb : d131081 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d131081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130390 q = 1) (hb : d131082 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d131082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130390 q = 1) (hb : d131083 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d131083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55940 (p : Pattern) (ha : d130390 p = 1) (hb : d131089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130390 q = 1) (hb : d131084 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d131084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55939 q ha hb
    | true =>
      simp only [d131084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130390 q = 1) (hb : d131085 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d131085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130390 q = 1) (hb : d131086 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d131086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130390 q = 1) (hb : d131087 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d131087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130390 q = 1) (hb : d131088 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d131088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130390 q = 1) (hb : d131089 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d131089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55941 (p : Pattern) (ha : d130390 p = 1) (hb : d131095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130390 q = 1) (hb : d131090 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d131090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55940 q ha hb
    | true =>
      simp only [d131090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130390 q = 1) (hb : d131091 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d131091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130390 q = 1) (hb : d131092 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d131092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130390 q = 1) (hb : d131093 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d131093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130390 q = 1) (hb : d131094 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d131094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130390 q = 1) (hb : d131095 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d131095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55942 (p : Pattern) (ha : d0 p = 1) (hb : d227505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d227505 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro55943 (p : Pattern) (ha : d130389 p = 1) (hb : d192722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20478 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55869 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192718 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192719 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192720 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192721 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192722 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55944 (p : Pattern) (ha : d130389 p = 1) (hb : d192732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20420 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55866 q ha hb
    | true =>
      simp only [d20420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55862 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192730 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192731 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192732 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55945 (p : Pattern) (ha : d130389 p = 1) (hb : d192738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192733 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55944 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192734 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192735 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192736 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192737 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192738 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55946 (p : Pattern) (ha : d130389 p = 1) (hb : d192744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192723 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55943 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192724 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192725 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192726 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192727 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192739 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55945 q ha hb
  have h7 (q : Pattern) (ha : d130389 q = 1) (hb : d192740 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130389 q = 1) (hb : d192741 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130389 q = 1) (hb : d192742 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130389 q = 1) (hb : d192743 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d130389 q = 1) (hb : d192744 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro55947 (p : Pattern) (ha : d130389 p = 1) (hb : d192750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192745 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55882 q hb ha
    | true =>
      simp only [d192745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55877 q hb ha
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192747 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192748 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192749 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192750 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55948 (p : Pattern) (ha : d130389 p = 1) (hb : d192756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192751 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55947 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192752 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192753 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192754 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192755 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192756 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55949 (p : Pattern) (ha : d130389 p = 1) (hb : d192762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192757 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55948 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192758 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192759 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192760 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192761 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192762 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55950 (p : Pattern) (ha : d130389 p = 1) (hb : d192769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55893 q hb ha
    | true =>
      simp only [d192764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55888 q hb ha
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192768 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192769 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55951 (p : Pattern) (ha : d130389 p = 1) (hb : d192775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192770 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55950 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192771 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192772 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192774 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192775 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55952 (p : Pattern) (ha : d130389 p = 1) (hb : d192781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192776 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55951 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192777 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192778 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192779 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192780 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192781 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55953 (p : Pattern) (ha : d130389 p = 1) (hb : d192784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16673 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d16674 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16674, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d16675 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16676 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d16677 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16677, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d16678 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16679 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16693 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16694 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16694, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d16695 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16696 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d130389 q = 1) (hb : d171139 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d171139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d9834 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23507 q ha hb
    | true =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d9835 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9835, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9836 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9851 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
    | true =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23509 q ha hb
  have h19 (q : Pattern) (ha : d9852 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9852, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h20 (q : Pattern) (ha : d9853 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9854 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d9870 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
    | true =>
      simp only [d9870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23502 q ha hb
  have h23 (q : Pattern) (ha : d9871 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9871, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9871, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h24 (q : Pattern) (ha : d9872 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d9873 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d9873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d129539 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d129539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d130389 q = 1) (hb : d192784 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d192784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d192784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  exact h27 p ha hb
theorem andIntro55954 (p : Pattern) (ha : d130389 p = 1) (hb : d192790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192785 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d192785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55953 q ha hb
    | true =>
      simp only [d192785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192786 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d192786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20638 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55898 q ha hb
    | true =>
      simp only [d20638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20639 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192787 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d192787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192788 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d192788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130389 q = 1) (hb : d192789 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d192789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130389 q = 1) (hb : d192790 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d192790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro55955 (p : Pattern) (ha : d130389 p = 1) (hb : d192796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192791 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55954 q ha hb
    | true =>
      simp only [d192791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55899 q hb ha
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192792 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192793 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192794 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192795 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192796 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55956 (p : Pattern) (ha : d130389 p = 1) (hb : d192802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192797 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55955 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192798 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192799 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192800 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192801 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192802 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55957 (p : Pattern) (ha : d130389 p = 1) (hb : d192808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192803 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55956 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192804 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192805 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192806 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192807 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192808 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55958 (p : Pattern) (ha : d130389 p = 1) (hb : d192812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17033 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17034 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17034, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17035 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17036 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17037 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17037, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d17038 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17039 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d17053 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17054 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17054, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d17055 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17056 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d130389 q = 1) (hb : d171176 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d171176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d10122 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23526 q ha hb
    | true =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10123 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10123, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10124 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10142 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
    | true =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23528 q ha hb
  have h19 (q : Pattern) (ha : d10143 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10143, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h20 (q : Pattern) (ha : d10144 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10145 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d10164 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
    | true =>
      simp only [d10164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23521 q ha hb
  have h23 (q : Pattern) (ha : d10165 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10165, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10165, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h24 (q : Pattern) (ha : d10166 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d10167 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d10167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d129568 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d129568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d130389 q = 1) (hb : d192812 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d192812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d192812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  exact h27 p ha hb
theorem andIntro55959 (p : Pattern) (ha : d130389 p = 1) (hb : d192818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192813 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d192813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55958 q ha hb
    | true =>
      simp only [d192813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192814 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d192814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20711 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55910 q ha hb
    | true =>
      simp only [d20711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20712 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192815 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d192815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192816 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d192816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130389 q = 1) (hb : d192817 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d192817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130389 q = 1) (hb : d192818 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d192818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro55960 (p : Pattern) (ha : d130389 p = 1) (hb : d192824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192819 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55959 q ha hb
    | true =>
      simp only [d192819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55911 q hb ha
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192820 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192821 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192822 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192823 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192824 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55961 (p : Pattern) (ha : d130389 p = 1) (hb : d192830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192825 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55960 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192826 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192827 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192828 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192829 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192830 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55962 (p : Pattern) (ha : d130389 p = 1) (hb : d192836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192831 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55961 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192832 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192833 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192834 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192835 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192836 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55963 (p : Pattern) (ha : d130389 p = 1) (hb : d192841 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17397 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17398 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17398, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d17399 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17400 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17401 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17401, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d17402 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17403 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d17417 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17418 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17418, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d17419 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17420 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d130389 q = 1) (hb : d171214 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d171214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d10398 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23545 q ha hb
    | true =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10399 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10399, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10400 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10419 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
    | true =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23547 q ha hb
  have h19 (q : Pattern) (ha : d10420 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10420, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h20 (q : Pattern) (ha : d10421 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10422 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d10441 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
    | true =>
      simp only [d10441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23540 q ha hb
  have h23 (q : Pattern) (ha : d10442 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10442, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10442, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h24 (q : Pattern) (ha : d10443 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d10444 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d10444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d129598 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d129598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d130389 q = 1) (hb : d192841 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d192841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d192841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  exact h27 p ha hb
theorem andIntro55964 (p : Pattern) (ha : d130389 p = 1) (hb : d192847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192842 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d192842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55963 q ha hb
    | true =>
      simp only [d192842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192843 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d192843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20785 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55922 q ha hb
    | true =>
      simp only [d20785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20786 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d192844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192845 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d192845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130389 q = 1) (hb : d192846 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d192846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130389 q = 1) (hb : d192847 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d192847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro55965 (p : Pattern) (ha : d130389 p = 1) (hb : d192853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192848 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55964 q ha hb
    | true =>
      simp only [d192848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55923 q hb ha
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192849 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192850 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192851 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192852 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192853 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55966 (p : Pattern) (ha : d130389 p = 1) (hb : d192859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192854 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55965 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192856 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192857 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192858 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192859 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55967 (p : Pattern) (ha : d130389 p = 1) (hb : d192865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192860 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55966 q ha hb
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192861 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192862 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192863 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192864 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192865 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro55968 (p : Pattern) (ha : d130389 p = 1) (hb : d192871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d130389 q = 1) (hb : d192763 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55946 q ha hb
    | true =>
      simp only [d192763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55949 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192782 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55952 q ha hb
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192783 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192809 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55957 q ha hb
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192810 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192811 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d192811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130389 q = 1) (hb : d192837 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55962 q ha hb
  have h8 (q : Pattern) (ha : d130389 q = 1) (hb : d192838 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130389 q = 1) (hb : d192839 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d192839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130389 q = 1) (hb : d192840 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d192840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d130389 q = 1) (hb : d192866 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55967 q ha hb
  have h12 (q : Pattern) (ha : d130389 q = 1) (hb : d192867 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d130389 q = 1) (hb : d192868 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d192868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d130389 q = 1) (hb : d192869 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d192869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d130389 q = 1) (hb : d192870 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d192870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d192870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d130389 q = 1) (hb : d192871 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d192871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d192871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro55969 (p : Pattern) (ha : d130389 p = 1) (hb : d192877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192872 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d192872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55968 q ha hb
    | true =>
      simp only [d192872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192873 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d192873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192874 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d192874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192875 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d192875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192876 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d192876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192877 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d192877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55970 (p : Pattern) (ha : d130389 p = 1) (hb : d192883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192878 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d192878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55969 q ha hb
    | true =>
      simp only [d192878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192879 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d192879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192880 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d192880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130389 q = 1) (hb : d192881 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d192881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130389 q = 1) (hb : d192882 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d192882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130389 q = 1) (hb : d192883 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d192883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55971 (p : Pattern) (ha : d130390 p = 1) (hb : d192889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130389 q = 1) (hb : d192884 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d192884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55970 q ha hb
    | true =>
      simp only [d192884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130389 q = 1) (hb : d192885 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d192885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130389 q = 1) (hb : d192886 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d192886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130390 q = 1) (hb : d192887 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d130390, d192887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130390, d192887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d130390 q = 1) (hb : d192888 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d192888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d130390 q = 1) (hb : d192889 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d192889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h8 p ha hb
theorem andIntro55972 (p : Pattern) (ha : d130390 p = 1) (hb : d192895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130390 q = 1) (hb : d192890 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d192890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55971 q ha hb
    | true =>
      simp only [d192890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130390 q = 1) (hb : d192891 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d192891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130390 q = 1) (hb : d192892 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d192892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130390 q = 1) (hb : d192893 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d192893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130390 q = 1) (hb : d192894 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d192894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130390 q = 1) (hb : d192895 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d192895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55973 (p : Pattern) (ha : d130390 p = 1) (hb : d192901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130390 q = 1) (hb : d192896 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d192896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55972 q ha hb
    | true =>
      simp only [d192896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130390 q = 1) (hb : d192897 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d192897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130390 q = 1) (hb : d192898 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d192898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130390 q = 1) (hb : d192899 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d192899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130390 q = 1) (hb : d192900 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d192900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130390 q = 1) (hb : d192901 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d192901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55974 (p : Pattern) (ha : d130390 p = 1) (hb : d192907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130390 q = 1) (hb : d192902 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d192902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55973 q ha hb
    | true =>
      simp only [d192902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130390 q = 1) (hb : d192903 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d192903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130390 q = 1) (hb : d192904 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d192904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130390 q = 1) (hb : d192905 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d192905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130390 q = 1) (hb : d192906 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d192906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130390 q = 1) (hb : d192907 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d192907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55975 (p : Pattern) (ha : d130390 p = 1) (hb : d192913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130390 q = 1) (hb : d192908 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d192908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55974 q ha hb
    | true =>
      simp only [d192908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130390 q = 1) (hb : d192909 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d192909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130390 q = 1) (hb : d192910 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d192910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130390 q = 1) (hb : d192911 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d192911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130390 q = 1) (hb : d192912 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d192912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130390 q = 1) (hb : d192913 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d192913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55976 (p : Pattern) (ha : d0 p = 1) (hb : d227681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d227681 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro55977 (p : Pattern) (ha : d131095 p = 1) (hb : d227682 p = 1) : d131095 p = 1 := by
  have h0 (q : Pattern) (ha : d131095 q = 1) (hb : d227682 q = 1) : d131095 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro55978 (p : Pattern) (ha : d192913 p = 1) (hb : d227682 p = 1) : d192913 p = 1 := by
  have h0 (q : Pattern) (ha : d192913 q = 1) (hb : d227682 q = 1) : d192913 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro55979 (p : Pattern) (ha : d131071 p = 1) (hb : d188524 p = 1) : d132739 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131066 q = 1) (hb : d131097 q = 1) : d132734 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d131066, d132734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55440 q ha hb
    | true =>
      simp only [d131066, d132734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131067 q = 1) (hb : d131097 q = 1) : d132735 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d131067, d132735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131067, d132735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131068 q = 1) (hb : d131097 q = 1) : d132736 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d131068, d132736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131068, d132736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131069 q = 1) (hb : d188522 q = 1) : d132737 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d131069, d188522, d132737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131069, d188522, d132737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d188523 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d131070 q = 1) (hb : d188524 q = 1) : d132738 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d131070, d188524, d132738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131070, d188524, d132738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d188524 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131071 q = 1) (hb : d188524 q = 1) : d132739 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d131071, d132739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131071, d132739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro55980 (p : Pattern) (ha : d131077 p = 1) (hb : d188524 p = 1) : d132745 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188524 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131072 q = 1) (hb : d188524 q = 1) : d132740 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d131072, d132740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55979 q ha hb
    | true =>
      simp only [d131072, d132740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131073 q = 1) (hb : d188524 q = 1) : d132741 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d131073, d132741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131073, d132741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131074 q = 1) (hb : d188524 q = 1) : d132742 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d131074, d132742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131074, d132742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131075 q = 1) (hb : d188524 q = 1) : d132743 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d131075, d132743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131075, d132743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131076 q = 1) (hb : d188524 q = 1) : d132744 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d131076, d132744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131076, d132744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131077 q = 1) (hb : d188524 q = 1) : d132745 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d131077, d132745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131077, d132745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55981 (p : Pattern) (ha : d131083 p = 1) (hb : d188524 p = 1) : d132751 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188524 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131078 q = 1) (hb : d188524 q = 1) : d132746 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d131078, d132746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55980 q ha hb
    | true =>
      simp only [d131078, d132746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131079 q = 1) (hb : d188524 q = 1) : d132747 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d131079, d132747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131079, d132747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131080 q = 1) (hb : d188524 q = 1) : d132748 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d131080, d132748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131080, d132748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131081 q = 1) (hb : d188524 q = 1) : d132749 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d131081, d132749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131081, d132749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131082 q = 1) (hb : d188524 q = 1) : d132750 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d131082, d132750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131082, d132750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131083 q = 1) (hb : d188524 q = 1) : d132751 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d131083, d132751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131083, d132751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55982 (p : Pattern) (ha : d131089 p = 1) (hb : d188524 p = 1) : d132757 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188524 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131084 q = 1) (hb : d188524 q = 1) : d132752 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d131084, d132752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55981 q ha hb
    | true =>
      simp only [d131084, d132752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131085 q = 1) (hb : d188524 q = 1) : d132753 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d131085, d132753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131085, d132753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131086 q = 1) (hb : d188524 q = 1) : d132754 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d131086, d132754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131086, d132754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131087 q = 1) (hb : d188524 q = 1) : d132755 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d131087, d132755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131087, d132755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131088 q = 1) (hb : d188524 q = 1) : d132756 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d131088, d132756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131088, d132756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131089 q = 1) (hb : d188524 q = 1) : d132757 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d131089, d132757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131089, d132757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55983 (p : Pattern) (ha : d131095 p = 1) (hb : d188524 p = 1) : d132763 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188524 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131090 q = 1) (hb : d188524 q = 1) : d132758 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d131090, d132758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55982 q ha hb
    | true =>
      simp only [d131090, d132758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131091 q = 1) (hb : d188524 q = 1) : d132759 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d131091, d132759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131091, d132759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131092 q = 1) (hb : d188524 q = 1) : d132760 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d131092, d132760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131092, d132760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131093 q = 1) (hb : d188524 q = 1) : d132761 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d131093, d132761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131093, d132761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131094 q = 1) (hb : d188524 q = 1) : d132762 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d131094, d132762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131094, d132762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131095 q = 1) (hb : d188524 q = 1) : d132763 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d131095, d132763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131095, d132763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55984 (p : Pattern) (ha : d188524 p = 1) (hb : d192889 p = 1) : d187854 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131097 q = 1) (hb : d192884 q = 1) : d187849 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d192884, d187849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55585 q ha hb
    | true =>
      simp only [d192884, d187849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131097 q = 1) (hb : d192885 q = 1) : d187850 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d192885, d187850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192885, d187850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131097 q = 1) (hb : d192886 q = 1) : d187851 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d192886, d187851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192886, d187851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d188522 q = 1) (hb : d192887 q = 1) : d187852 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d188522, d192887, d187852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188522, d192887, d187852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d188523 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d188524 q = 1) (hb : d192888 q = 1) : d187853 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d188524, d192888, d187853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188524, d192888, d187853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d188524 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d188524 q = 1) (hb : d192889 q = 1) : d187854 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d192889, d187854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192889, d187854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro55985 (p : Pattern) (ha : d188524 p = 1) (hb : d192895 p = 1) : d187860 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188524 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188524 q = 1) (hb : d192890 q = 1) : d187855 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d192890, d187855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55984 q ha hb
    | true =>
      simp only [d192890, d187855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d188524 q = 1) (hb : d192891 q = 1) : d187856 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d192891, d187856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192891, d187856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d188524 q = 1) (hb : d192892 q = 1) : d187857 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d192892, d187857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192892, d187857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188524 q = 1) (hb : d192893 q = 1) : d187858 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d192893, d187858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192893, d187858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d188524 q = 1) (hb : d192894 q = 1) : d187859 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d192894, d187859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192894, d187859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d188524 q = 1) (hb : d192895 q = 1) : d187860 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d192895, d187860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192895, d187860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55986 (p : Pattern) (ha : d188524 p = 1) (hb : d192901 p = 1) : d187866 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188524 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188524 q = 1) (hb : d192896 q = 1) : d187861 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d192896, d187861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55985 q ha hb
    | true =>
      simp only [d192896, d187861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d188524 q = 1) (hb : d192897 q = 1) : d187862 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d192897, d187862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192897, d187862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d188524 q = 1) (hb : d192898 q = 1) : d187863 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d192898, d187863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192898, d187863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188524 q = 1) (hb : d192899 q = 1) : d187864 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d192899, d187864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192899, d187864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d188524 q = 1) (hb : d192900 q = 1) : d187865 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d192900, d187865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192900, d187865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d188524 q = 1) (hb : d192901 q = 1) : d187866 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d192901, d187866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192901, d187866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55987 (p : Pattern) (ha : d188524 p = 1) (hb : d192907 p = 1) : d187872 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188524 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188524 q = 1) (hb : d192902 q = 1) : d187867 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d192902, d187867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55986 q ha hb
    | true =>
      simp only [d192902, d187867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d188524 q = 1) (hb : d192903 q = 1) : d187868 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d192903, d187868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192903, d187868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d188524 q = 1) (hb : d192904 q = 1) : d187869 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d192904, d187869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192904, d187869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188524 q = 1) (hb : d192905 q = 1) : d187870 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d192905, d187870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192905, d187870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d188524 q = 1) (hb : d192906 q = 1) : d187871 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d192906, d187871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192906, d187871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d188524 q = 1) (hb : d192907 q = 1) : d187872 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d192907, d187872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192907, d187872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55988 (p : Pattern) (ha : d188524 p = 1) (hb : d192913 p = 1) : d187878 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188524 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d188524 q = 1) (hb : d192908 q = 1) : d187873 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d192908, d187873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55987 q ha hb
    | true =>
      simp only [d192908, d187873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d188524 q = 1) (hb : d192909 q = 1) : d187874 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d192909, d187874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192909, d187874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d188524 q = 1) (hb : d192910 q = 1) : d187875 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d192910, d187875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192910, d187875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d188524 q = 1) (hb : d192911 q = 1) : d187876 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d192911, d187876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192911, d187876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d188524 q = 1) (hb : d192912 q = 1) : d187877 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d192912, d187877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192912, d187877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d188524 q = 1) (hb : d192913 q = 1) : d187878 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d192913, d187878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192913, d187878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55989 (p : Pattern) (ha : d131071 p = 1) (hb : d192710 p = 1) : d130362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d131066 q = 1) : d130357 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d131066, d130357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45072 q ha hb
    | true =>
      simp only [d131066, d130357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d131067 q = 1) : d130358 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d131067, d130358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131067, d130358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131068 q = 1) (hb : d192710 q = 1) : d130359 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d131068, d192710, d130359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131068, d192710, d130359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d192710 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d131069 q = 1) (hb : d192710 q = 1) : d130360 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d131069, d130360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131069, d130360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131070 q = 1) (hb : d192710 q = 1) : d130361 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d131070, d130361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131070, d130361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d131071 q = 1) (hb : d192710 q = 1) : d130362 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d131071, d130362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131071, d130362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro55990 (p : Pattern) (ha : d131077 p = 1) (hb : d192712 p = 1) : d130368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d192710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131072 q = 1) (hb : d192710 q = 1) : d130363 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d131072, d130363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55989 q ha hb
    | true =>
      simp only [d131072, d130363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d192711 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131073 q = 1) (hb : d192712 q = 1) : d130364 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d131073, d192712, d130364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131073, d192712, d130364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d192712 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131074 q = 1) (hb : d192712 q = 1) : d130365 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d131074, d130365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131074, d130365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131075 q = 1) (hb : d192712 q = 1) : d130366 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d131075, d130366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131075, d130366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d131076 q = 1) (hb : d192712 q = 1) : d130367 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d131076, d130367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131076, d130367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d131077 q = 1) (hb : d192712 q = 1) : d130368 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d131077, d130368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131077, d130368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h8 p ha hb
theorem andIntro55991 (p : Pattern) (ha : d131083 p = 1) (hb : d192712 p = 1) : d130374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d192712 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131078 q = 1) (hb : d192712 q = 1) : d130369 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d131078, d130369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55990 q ha hb
    | true =>
      simp only [d131078, d130369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131079 q = 1) (hb : d192712 q = 1) : d130370 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d131079, d130370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131079, d130370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131080 q = 1) (hb : d192712 q = 1) : d130371 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d131080, d130371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131080, d130371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131081 q = 1) (hb : d192712 q = 1) : d130372 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d131081, d130372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131081, d130372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131082 q = 1) (hb : d192712 q = 1) : d130373 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d131082, d130373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131082, d130373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131083 q = 1) (hb : d192712 q = 1) : d130374 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d131083, d130374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131083, d130374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55992 (p : Pattern) (ha : d131089 p = 1) (hb : d192712 p = 1) : d130380 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d192712 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131084 q = 1) (hb : d192712 q = 1) : d130375 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d131084, d130375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55991 q ha hb
    | true =>
      simp only [d131084, d130375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131085 q = 1) (hb : d192712 q = 1) : d130376 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d131085, d130376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131085, d130376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131086 q = 1) (hb : d192712 q = 1) : d130377 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d131086, d130377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131086, d130377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131087 q = 1) (hb : d192712 q = 1) : d130378 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d131087, d130378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131087, d130378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131088 q = 1) (hb : d192712 q = 1) : d130379 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d131088, d130379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131088, d130379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131089 q = 1) (hb : d192712 q = 1) : d130380 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d131089, d130380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131089, d130380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55993 (p : Pattern) (ha : d131095 p = 1) (hb : d192712 p = 1) : d130386 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d192712 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131090 q = 1) (hb : d192712 q = 1) : d130381 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d131090, d130381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55992 q ha hb
    | true =>
      simp only [d131090, d130381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131091 q = 1) (hb : d192712 q = 1) : d130382 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d131091, d130382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131091, d130382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131092 q = 1) (hb : d192712 q = 1) : d130383 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d131092, d130383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131092, d130383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131093 q = 1) (hb : d192712 q = 1) : d130384 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d131093, d130384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131093, d130384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131094 q = 1) (hb : d192712 q = 1) : d130385 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d131094, d130385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131094, d130385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131095 q = 1) (hb : d192712 q = 1) : d130386 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d131095, d130386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131095, d130386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro55994 (p : Pattern) (ha : d192710 p = 1) (hb : d192889 p = 1) : d188699 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192884 q = 1) : d188694 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d192884, d188694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45186 q ha hb
    | true =>
      simp only [d192884, d188694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192885 q = 1) : d188695 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d192885, d188695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192885, d188695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d192710 q = 1) (hb : d192886 q = 1) : d188696 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d192710, d192886, d188696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192710, d192886, d188696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d192710 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d192710 q = 1) (hb : d192887 q = 1) : d188697 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d192887, d188697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192887, d188697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d192710 q = 1) (hb : d192888 q = 1) : d188698 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d192888, d188698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192888, d188698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h8 (q : Pattern) (ha : d192710 q = 1) (hb : d192889 q = 1) : d188699 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d192889, d188699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192889, d188699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h8 p ha hb
theorem andIntro55995 (p : Pattern) (ha : d192712 p = 1) (hb : d192895 p = 1) : d188705 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d192710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192710 q = 1) (hb : d192890 q = 1) : d188700 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d192890, d188700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55994 q ha hb
    | true =>
      simp only [d192890, d188700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d192711 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d192712 q = 1) (hb : d192891 q = 1) : d188701 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d192712, d192891, d188701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192712, d192891, d188701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d192712 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d192712 q = 1) (hb : d192892 q = 1) : d188702 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d192892, d188702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192892, d188702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d192712 q = 1) (hb : d192893 q = 1) : d188703 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d192893, d188703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192893, d188703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h7 (q : Pattern) (ha : d192712 q = 1) (hb : d192894 q = 1) : d188704 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d192894, d188704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192894, d188704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h8 (q : Pattern) (ha : d192712 q = 1) (hb : d192895 q = 1) : d188705 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d192895, d188705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192895, d188705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h8 p ha hb
theorem andIntro55996 (p : Pattern) (ha : d192712 p = 1) (hb : d192901 p = 1) : d188711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d192712 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192712 q = 1) (hb : d192896 q = 1) : d188706 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d192896, d188706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55995 q ha hb
    | true =>
      simp only [d192896, d188706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d192712 q = 1) (hb : d192897 q = 1) : d188707 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d192897, d188707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192897, d188707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d192712 q = 1) (hb : d192898 q = 1) : d188708 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d192898, d188708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192898, d188708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d192712 q = 1) (hb : d192899 q = 1) : d188709 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d192899, d188709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192899, d188709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d192712 q = 1) (hb : d192900 q = 1) : d188710 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d192900, d188710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192900, d188710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d192712 q = 1) (hb : d192901 q = 1) : d188711 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d192901, d188711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192901, d188711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55997 (p : Pattern) (ha : d192712 p = 1) (hb : d192907 p = 1) : d188717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d192712 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192712 q = 1) (hb : d192902 q = 1) : d188712 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d192902, d188712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55996 q ha hb
    | true =>
      simp only [d192902, d188712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d192712 q = 1) (hb : d192903 q = 1) : d188713 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d192903, d188713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192903, d188713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d192712 q = 1) (hb : d192904 q = 1) : d188714 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d192904, d188714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192904, d188714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d192712 q = 1) (hb : d192905 q = 1) : d188715 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d192905, d188715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192905, d188715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d192712 q = 1) (hb : d192906 q = 1) : d188716 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d192906, d188716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192906, d188716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d192712 q = 1) (hb : d192907 q = 1) : d188717 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d192907, d188717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192907, d188717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55998 (p : Pattern) (ha : d192712 p = 1) (hb : d192913 p = 1) : d188723 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d192712 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192712 q = 1) (hb : d192908 q = 1) : d188718 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d192908, d188718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55997 q ha hb
    | true =>
      simp only [d192908, d188718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d192712 q = 1) (hb : d192909 q = 1) : d188719 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d192909, d188719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192909, d188719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d192712 q = 1) (hb : d192910 q = 1) : d188720 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d192910, d188720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192910, d188720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d192712 q = 1) (hb : d192911 q = 1) : d188721 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d192911, d188721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192911, d188721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d192712 q = 1) (hb : d192912 q = 1) : d188722 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d192912, d188722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192912, d188722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d192712 q = 1) (hb : d192913 q = 1) : d188723 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d192913, d188723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192913, d188723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro55999 (p : Pattern) (ha : d74849 p = 1) (hb : d194336 p = 1) : d74849 p = 1 := by
  have h0 (q : Pattern) (ha : d74849 q = 1) (hb : d194336 q = 1) : d74849 q = 1 := by
    exact ha
  exact h0 p ha hb
end NetHack.Soko22Hazard87
