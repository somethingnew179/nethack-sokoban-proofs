import NetHack.Soko22Hazard87.AndIntroBlocks0043
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro11000 (p : Pattern) (ha : d82206 p = 1) (hb : d82806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7055 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6413 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6414 q = 1) (hb : d82195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6414, d82195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6414, d82195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6467 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6415 q = 1) (hb : d82196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6415, d82196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6415, d82196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6416 q = 1) (hb : d82204 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6416, d82204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6416, d82204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6417 q = 1) (hb : d82205 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6417, d82205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6417, d82205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82206 q = 1) (hb : d82806 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82206, d82806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82206, d82806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro11001 (p : Pattern) (ha : d82216 p = 1) (hb : d82817 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7093 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d82812 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d82212 q = 1) (hb : d82813 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82212, d82813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82212, d82813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6526 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82213 q = 1) (hb : d82814 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82213, d82814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82213, d82814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d82214 q = 1) (hb : d82815 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82214, d82815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82214, d82815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82215 q = 1) (hb : d82816 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82215, d82816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82215, d82816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82216 q = 1) (hb : d82817 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82216, d82817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82216, d82817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11002 (p : Pattern) (ha : d82222 p = 1) (hb : d82823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6419 q = 1) (hb : d82200 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6419, d82200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10998 q ha hb
    | true =>
      simp only [d6419, d82200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10999 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7068 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6420 q = 1) (hb : d82201 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6420, d82201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6420, d82201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82202 q = 1) (hb : d82804 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82202, d82804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d82202, d82804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82203 q = 1) (hb : d82805 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82203, d82805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82203, d82805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82207 q = 1) (hb : d82807 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82207, d82807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82207, d82807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11000 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1848 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d82208 q = 1) (hb : d82808 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82208, d82808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82208, d82808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d82209 q = 1) (hb : d82809 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82209, d82809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82209, d82809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d82210 q = 1) (hb : d82810 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82210, d82810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82210, d82810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d82211 q = 1) (hb : d82811 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82211, d82811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82211, d82811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82217 q = 1) (hb : d82818 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82217, d82818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82217, d82818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11001 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d82218 q = 1) (hb : d82819 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82218, d82819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82218, d82819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d82219 q = 1) (hb : d82820 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82219, d82820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82219, d82820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d82220 q = 1) (hb : d82821 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82220, d82821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82220, d82821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d82221 q = 1) (hb : d82822 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82221, d82822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82221, d82822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d82222 q = 1) (hb : d82823 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82222, d82823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82222, d82823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro11003 (p : Pattern) (ha : d82228 p = 1) (hb : d82829 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82223 q = 1) (hb : d82824 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82223, d82824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82223, d82824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11002 q ha hb
  have h2 (q : Pattern) (ha : d82224 q = 1) (hb : d82825 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82224, d82825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82224, d82825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82225 q = 1) (hb : d82826 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82225, d82826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82225, d82826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82226 q = 1) (hb : d82827 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82226, d82827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82226, d82827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82227 q = 1) (hb : d82828 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82227, d82828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82227, d82828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82228 q = 1) (hb : d82829 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82228, d82829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82228, d82829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11004 (p : Pattern) (ha : d6556 p = 1) (hb : d82237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2133 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2142 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7128 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6551 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6552 q = 1) (hb : d82233 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6552, d82233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6552, d82233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6593 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6553 q = 1) (hb : d82234 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6553, d82234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6553, d82234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6554 q = 1) (hb : d82235 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6554, d82235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6554, d82235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6555 q = 1) (hb : d82236 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6555, d82236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6555, d82236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6556 q = 1) (hb : d82237 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6556, d82237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6556, d82237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11005 (p : Pattern) (ha : d6565 p = 1) (hb : d82242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2133 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2142 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7128 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6551 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6552 q = 1) (hb : d82233 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6552, d82233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6552, d82233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6593 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6553 q = 1) (hb : d82234 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6553, d82234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6553, d82234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6554 q = 1) (hb : d82235 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6554, d82235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6554, d82235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6555 q = 1) (hb : d82236 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6555, d82236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6555, d82236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d2286 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d2291 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7136 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d6560 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d6561 q = 1) (hb : d82238 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6561, d82238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6561, d82238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6614 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6562 q = 1) (hb : d82239 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6562, d82239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6562, d82239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d6563 q = 1) (hb : d82240 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6563, d82240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d6563, d82240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d6564 q = 1) (hb : d82241 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6564, d82241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6564, d82241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d6565 q = 1) (hb : d82242 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6565, d82242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6565, d82242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro11006 (p : Pattern) (ha : d82249 p = 1) (hb : d82836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7136 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6560 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6561 q = 1) (hb : d82238 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6561, d82238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6561, d82238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6614 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6562 q = 1) (hb : d82239 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6562, d82239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6562, d82239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6563 q = 1) (hb : d82247 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6563, d82247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6563, d82247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6564 q = 1) (hb : d82248 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6564, d82248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6564, d82248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82249 q = 1) (hb : d82836 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82249, d82836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82249, d82836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro11007 (p : Pattern) (ha : d82259 p = 1) (hb : d82847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7174 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d82842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d82255 q = 1) (hb : d82843 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82255, d82843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82255, d82843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6673 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82256 q = 1) (hb : d82844 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82256, d82844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82256, d82844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d82257 q = 1) (hb : d82845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82257, d82845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82257, d82845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82258 q = 1) (hb : d82846 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82258, d82846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82258, d82846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82259 q = 1) (hb : d82847 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82259, d82847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82259, d82847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11008 (p : Pattern) (ha : d82265 p = 1) (hb : d82853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2125 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6566 q = 1) (hb : d82243 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6566, d82243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11004 q ha hb
    | true =>
      simp only [d6566, d82243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11005 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7149 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6567 q = 1) (hb : d82244 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6567, d82244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6567, d82244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d82245 q = 1) (hb : d82834 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82245, d82834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d82245, d82834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82246 q = 1) (hb : d82835 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82246, d82835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82246, d82835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82250 q = 1) (hb : d82837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82250, d82837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82250, d82837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11006 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2326 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d82251 q = 1) (hb : d82838 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82251, d82838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82251, d82838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d82252 q = 1) (hb : d82839 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82252, d82839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82252, d82839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d82253 q = 1) (hb : d82840 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82253, d82840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82253, d82840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d82254 q = 1) (hb : d82841 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82254, d82841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82254, d82841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82260 q = 1) (hb : d82848 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82260, d82848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82260, d82848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11007 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d2459 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d82261 q = 1) (hb : d82849 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82261, d82849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82261, d82849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d82262 q = 1) (hb : d82850 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82262, d82850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82262, d82850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d82263 q = 1) (hb : d82851 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82263, d82851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82263, d82851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d82264 q = 1) (hb : d82852 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82264, d82852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82264, d82852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d82265 q = 1) (hb : d82853 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82265, d82853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82265, d82853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro11009 (p : Pattern) (ha : d82271 p = 1) (hb : d82859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82266 q = 1) (hb : d82854 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82266, d82854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82266, d82854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11008 q ha hb
  have h2 (q : Pattern) (ha : d82267 q = 1) (hb : d82855 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82267, d82855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82267, d82855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82268 q = 1) (hb : d82856 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82268, d82856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82268, d82856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82269 q = 1) (hb : d82857 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82269, d82857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82269, d82857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82270 q = 1) (hb : d82858 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82270, d82858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82270, d82858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82271 q = 1) (hb : d82859 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82271, d82859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82271, d82859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11010 (p : Pattern) (ha : d82277 p = 1) (hb : d82865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d82106 q = 1) (hb : d82746 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82106, d82746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10979 q ha hb
    | true =>
      simp only [d82106, d82746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10985 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d82146 q = 1) (hb : d82773 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82146, d82773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82146, d82773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10991 q ha hb
  have h3 (q : Pattern) (ha : d82147 q = 1) (hb : d82774 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82147, d82774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82147, d82774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82187 q = 1) (hb : d82801 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82187, d82801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82187, d82801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10997 q ha hb
  have h5 (q : Pattern) (ha : d82188 q = 1) (hb : d82802 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82188, d82802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82188, d82802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82189 q = 1) (hb : d82803 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82189, d82803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82189, d82803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82229 q = 1) (hb : d82830 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82229, d82830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82229, d82830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11003 q ha hb
  have h8 (q : Pattern) (ha : d82230 q = 1) (hb : d82831 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82230, d82831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82230, d82831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d82231 q = 1) (hb : d82832 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82231, d82832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82231, d82832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82232 q = 1) (hb : d82833 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d82232, d82833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82232, d82833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d82272 q = 1) (hb : d82860 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82272, d82860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82272, d82860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11009 q ha hb
  have h12 (q : Pattern) (ha : d82273 q = 1) (hb : d82861 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82273, d82861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82273, d82861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82274 q = 1) (hb : d82862 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82274, d82862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82274, d82862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d82275 q = 1) (hb : d82863 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d82275, d82863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82275, d82863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82276 q = 1) (hb : d82864 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d82276, d82864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82276, d82864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d82277 q = 1) (hb : d82865 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d82277, d82865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82277, d82865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro11011 (p : Pattern) (ha : d82283 p = 1) (hb : d82871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82278 q = 1) (hb : d82866 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d82278, d82866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11010 q ha hb
    | true =>
      simp only [d82278, d82866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82279 q = 1) (hb : d82867 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d82279, d82867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82279, d82867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82280 q = 1) (hb : d82868 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d82280, d82868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82280, d82868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82281 q = 1) (hb : d82869 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d82281, d82869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82281, d82869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82282 q = 1) (hb : d82870 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d82282, d82870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82282, d82870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82283 q = 1) (hb : d82871 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d82283, d82871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82283, d82871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11012 (p : Pattern) (ha : d82289 p = 1) (hb : d82877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82284 q = 1) (hb : d82872 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d82284, d82872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11011 q ha hb
    | true =>
      simp only [d82284, d82872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82285 q = 1) (hb : d82873 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d82285, d82873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82285, d82873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82286 q = 1) (hb : d82874 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d82286, d82874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82286, d82874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82287 q = 1) (hb : d82875 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d82287, d82875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82287, d82875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82288 q = 1) (hb : d82876 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d82288, d82876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82288, d82876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82289 q = 1) (hb : d82877 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d82289, d82877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82289, d82877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11013 (p : Pattern) (ha : d82295 p = 1) (hb : d82883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82290 q = 1) (hb : d82878 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d82290, d82878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11012 q ha hb
    | true =>
      simp only [d82290, d82878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82291 q = 1) (hb : d82879 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d82291, d82879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82291, d82879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82292 q = 1) (hb : d82880 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d82292, d82880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82292, d82880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82293 q = 1) (hb : d82881 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d82293, d82881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82293, d82881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82294 q = 1) (hb : d82882 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d82294, d82882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82294, d82882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82295 q = 1) (hb : d82883 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d82295, d82883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82295, d82883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11014 (p : Pattern) (ha : d82301 p = 1) (hb : d82889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82296 q = 1) (hb : d82884 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d82296, d82884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11013 q ha hb
    | true =>
      simp only [d82296, d82884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82297 q = 1) (hb : d82885 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d82297, d82885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82297, d82885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82298 q = 1) (hb : d82886 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d82298, d82886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82298, d82886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82299 q = 1) (hb : d82887 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d82299, d82887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82299, d82887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82300 q = 1) (hb : d82888 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d82300, d82888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82300, d82888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82301 q = 1) (hb : d82889 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d82301, d82889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82301, d82889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11015 (p : Pattern) (ha : d82307 p = 1) (hb : d82895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82302 q = 1) (hb : d82890 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d82302, d82890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11014 q ha hb
    | true =>
      simp only [d82302, d82890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82303 q = 1) (hb : d82891 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d82303, d82891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82303, d82891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82304 q = 1) (hb : d82892 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d82304, d82892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82304, d82892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82305 q = 1) (hb : d82893 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d82305, d82893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82305, d82893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82306 q = 1) (hb : d82894 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d82306, d82894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82306, d82894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82307 q = 1) (hb : d82895 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d82307, d82895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82307, d82895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11016 (p : Pattern) (ha : d82313 p = 1) (hb : d82901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82308 q = 1) (hb : d82896 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d82308, d82896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11015 q ha hb
    | true =>
      simp only [d82308, d82896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82309 q = 1) (hb : d82897 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d82309, d82897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82309, d82897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82310 q = 1) (hb : d82898 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d82310, d82898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82310, d82898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82311 q = 1) (hb : d82899 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d82311, d82899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82311, d82899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82312 q = 1) (hb : d82900 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d82312, d82900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82312, d82900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82313 q = 1) (hb : d82901 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d82313, d82901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82313, d82901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11017 (p : Pattern) (ha : d82319 p = 1) (hb : d82907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82314 q = 1) (hb : d82902 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d82314, d82902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11016 q ha hb
    | true =>
      simp only [d82314, d82902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82315 q = 1) (hb : d82903 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d82315, d82903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82315, d82903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82316 q = 1) (hb : d82904 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d82316, d82904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82316, d82904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82317 q = 1) (hb : d82905 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d82317, d82905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82317, d82905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82318 q = 1) (hb : d82906 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d82318, d82906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82318, d82906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82319 q = 1) (hb : d82907 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d82319, d82907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82319, d82907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11018 (p : Pattern) (ha : d77100 p = 1) (hb : d89603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77096 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d89602 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d77097 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d77097, d89603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77097, d89603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d77098 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d77098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77099 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d77099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d77100 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d77100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro11019 (p : Pattern) (ha : d77106 p = 1) (hb : d89603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77101 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d77101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11018 q ha hb
    | true =>
      simp only [d77101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77102 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d77102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77103 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d77103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77104 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d77104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77105 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d77105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77106 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d77106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11020 (p : Pattern) (ha : d77112 p = 1) (hb : d89603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77107 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d77107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11019 q ha hb
    | true =>
      simp only [d77107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77108 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d77108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77109 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d77109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77110 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d77110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77111 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d77111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77112 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d77112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11021 (p : Pattern) (ha : d0 p = 1) (hb : d91979 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d91979 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro11022 (p : Pattern) (ha : d82895 p = 1) (hb : d89603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82891 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d89602 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d82892 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d82892, d89603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82892, d89603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d82893 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d82893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82894 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d82894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d82895 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d82895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro11023 (p : Pattern) (ha : d82901 p = 1) (hb : d89603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82896 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d82896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11022 q ha hb
    | true =>
      simp only [d82896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82897 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d82897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82898 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d82898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82899 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d82899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82900 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d82900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82901 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d82901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11024 (p : Pattern) (ha : d82907 p = 1) (hb : d89603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82902 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d82902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11023 q ha hb
    | true =>
      simp only [d82902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82903 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d82903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82904 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d82904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82905 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d82905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82906 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d82906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82907 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d82907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro11025 (p : Pattern) (ha : d0 p = 1) (hb : d92308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92308 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro11026 (p : Pattern) (ha : d104 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d100 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d103 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d104 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
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
theorem andIntro11027 (p : Pattern) (ha : d111 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d100 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d103 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d107 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d108 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d109 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d110 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d111 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
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
theorem andIntro11028 (p : Pattern) (ha : d213 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d100 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d103 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d213 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
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
theorem andIntro11029 (p : Pattern) (ha : d75630 p = 1) (hb : d76787 p = 1) : d76455 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d117 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d118 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d119 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d124 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d125 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d126 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4736 q = 1) (hb : d70145 q = 1) : d4736 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d42 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5850 q = 1) (hb : d75629 q = 1) : d4737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d75629, d4737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5850, d75629, d4737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d76783 q = 1) : d5350 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76783, d5350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d75630, d76783, d5350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44 q = 1) (hb : d75630 q = 1) : d44 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d76784 q = 1) : d76452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76784, d76452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76784, d76452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d76785 q = 1) : d76453 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76785, d76453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d76785, d76453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75630 q = 1) (hb : d76786 q = 1) : d76454 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76786, d76454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d76786, d76454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d75630 q = 1) (hb : d76787 q = 1) : d76455 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76787, d76455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76787, d76455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro11030 (p : Pattern) (ha : d75630 p = 1) (hb : d76792 p = 1) : d76459 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d117 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d118 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d119 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d124 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d125 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d126 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4736 q = 1) (hb : d70145 q = 1) : d4736 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d42 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5850 q = 1) (hb : d75629 q = 1) : d4737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d75629, d4737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5850, d75629, d4737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d76783 q = 1) : d5350 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76783, d5350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d75630, d76783, d5350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44 q = 1) (hb : d75630 q = 1) : d44 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d76784 q = 1) : d76452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76784, d76452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76784, d76452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d76785 q = 1) : d76453 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76785, d76453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d76785, d76453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75630 q = 1) (hb : d76786 q = 1) : d76454 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76786, d76454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d76786, d76454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d195 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d196 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d197 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d198 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d200 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d201 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d202 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d5355 q = 1) (hb : d70145 q = 1) : d5355 q = 1 := by
    exact ha
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d49 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d5856 q = 1) (hb : d75629 q = 1) : d5356 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5856, d75629, d5356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d5856, d75629, d5356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d75630 q = 1) (hb : d76788 q = 1) : d5357 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76788, d5357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
    | true =>
      simp only [d75630, d76788, d5357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h29 (q : Pattern) (ha : d51 q = 1) (hb : d75630 q = 1) : d51 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d75630 q = 1) (hb : d76789 q = 1) : d76456 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76789, d76456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d76789, d76456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d75630 q = 1) (hb : d76790 q = 1) : d76457 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76790, d76457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d76790, d76457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d75630 q = 1) (hb : d76791 q = 1) : d76458 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76791, d76458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d76791, d76458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d75630 q = 1) (hb : d76792 q = 1) : d76459 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76792, d76459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76792, d76459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro11031 (p : Pattern) (ha : d75630 p = 1) (hb : d76799 p = 1) : d76464 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5355 q = 1) (hb : d70145 q = 1) : d5355 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d49 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5856 q = 1) (hb : d75629 q = 1) : d5356 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5856, d75629, d5356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5856, d75629, d5356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d76788 q = 1) : d5357 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76788, d5357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d75630, d76788, d5357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51 q = 1) (hb : d75630 q = 1) : d51 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d76789 q = 1) : d76456 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76789, d76456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76789, d76456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d76797 q = 1) : d76457 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76797, d76457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76797, d76457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d76798 q = 1) : d76458 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76798, d76458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76798, d76458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d76799 q = 1) : d76464 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76799, d76464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76799, d76464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11032 (p : Pattern) (ha : d75630 p = 1) (hb : d76809 p = 1) : d76473 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5377 q = 1) (hb : d70145 q = 1) : d5377 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5874 q = 1) (hb : d75629 q = 1) : d5378 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5874, d75629, d5378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5874, d75629, d5378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d76805 q = 1) : d5379 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76805, d5379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d75630, d76805, d5379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85 q = 1) (hb : d75630 q = 1) : d85 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d76806 q = 1) : d76470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76806, d76470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76806, d76470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d76807 q = 1) : d76471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76807, d76471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76807, d76471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d76808 q = 1) : d76472 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76808, d76472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76808, d76472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d76809 q = 1) : d76473 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76809, d76473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76809, d76473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11033 (p : Pattern) (ha : d75630 p = 1) (hb : d76815 p = 1) : d76479 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11026 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11026 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11027 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d76793 q = 1) : d76460 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76793, d76460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11029 q ha hb
    | true =>
      simp only [d76793, d76460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11030 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11028 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d76794 q = 1) : d76461 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76794, d76461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76794, d76461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d76795 q = 1) : d76462 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76795, d76462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76795, d76462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d76796 q = 1) : d76463 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76796, d76463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d76796, d76463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75630 q = 1) (hb : d76800 q = 1) : d76465 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76800, d76465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76800, d76465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11031 q ha hb
  have h12 (q : Pattern) (ha : d75630 q = 1) (hb : d76801 q = 1) : d76466 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76801, d76466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76801, d76466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d76802 q = 1) : d76467 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76802, d76467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76802, d76467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d75630 q = 1) (hb : d76803 q = 1) : d76468 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76803, d76468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76803, d76468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d76804 q = 1) : d76469 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76804, d76469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76804, d76469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d76810 q = 1) : d76474 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76810, d76474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76810, d76474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11032 q ha hb
  have h17 (q : Pattern) (ha : d75630 q = 1) (hb : d76811 q = 1) : d76475 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76811, d76475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76811, d76475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d75630 q = 1) (hb : d76812 q = 1) : d76476 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76812, d76476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76812, d76476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d75630 q = 1) (hb : d76813 q = 1) : d76477 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76813, d76477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d76813, d76477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d75630 q = 1) (hb : d76814 q = 1) : d76478 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76814, d76478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76814, d76478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d75630 q = 1) (hb : d76815 q = 1) : d76479 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76815, d76479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76815, d76479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro11034 (p : Pattern) (ha : d406 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d110 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d406 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
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
theorem andIntro11035 (p : Pattern) (ha : d462 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d459 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d460 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d461 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d462 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
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
theorem andIntro11036 (p : Pattern) (ha : d5895 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5850 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5891 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5891, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5892 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5893 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5894 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5895 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11037 (p : Pattern) (ha : d5902 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5850 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5891 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5891, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5892 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5893 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5894 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d5856 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5898 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5898, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5898, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d5899 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5900 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5901 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5902 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro11038 (p : Pattern) (ha : d5952 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5850 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5891 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5891, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5892 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5893 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5894 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d100 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d101 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d102 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d103 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5952 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro11039 (p : Pattern) (ha : d75630 p = 1) (hb : d76825 p = 1) : d76490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5908 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5909 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5909, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5909, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5910 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5911 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5915 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5916 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5916, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5916, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d5917 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d5921 q = 1) (hb : d70145 q = 1) : d5921 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d4736 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5922 q = 1) (hb : d75629 q = 1) : d76485 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5922, d75629, d76485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5922, d75629, d76485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d76821 q = 1) : d76486 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76821, d76486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d75630, d76821, d76486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5350 q = 1) (hb : d75630 q = 1) : d5350 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d76822 q = 1) : d76487 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76822, d76487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76822, d76487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d76823 q = 1) : d76488 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76823, d76488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d76823, d76488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75630 q = 1) (hb : d76824 q = 1) : d76489 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76824, d76489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d76824, d76489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d75630 q = 1) (hb : d76825 q = 1) : d76490 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76825, d76490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76825, d76490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro11040 (p : Pattern) (ha : d75630 p = 1) (hb : d76830 p = 1) : d76496 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5908 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5909 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5909, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5909, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5910 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5911 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5915 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5916 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5916, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5916, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d5917 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d5921 q = 1) (hb : d70145 q = 1) : d5921 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d4736 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5922 q = 1) (hb : d75629 q = 1) : d76485 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5922, d75629, d76485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5922, d75629, d76485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d76821 q = 1) : d76486 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76821, d76486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d75630, d76821, d76486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5350 q = 1) (hb : d75630 q = 1) : d5350 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d76822 q = 1) : d76487 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76822, d76487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76822, d76487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d76823 q = 1) : d76488 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76823, d76488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d76823, d76488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75630 q = 1) (hb : d76824 q = 1) : d76489 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76824, d76489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d76824, d76489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d5934 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d5935 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5935, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5935, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d5936 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d5936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d5937 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d5939 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d5940 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5940, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5940, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d5941 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d5941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d5942 q = 1) (hb : d70145 q = 1) : d5942 q = 1 := by
    exact ha
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d5355 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d5943 q = 1) (hb : d75629 q = 1) : d76491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5943, d75629, d76491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d5943, d75629, d76491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d75630 q = 1) (hb : d76826 q = 1) : d76492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76826, d76492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
    | true =>
      simp only [d75630, d76826, d76492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h29 (q : Pattern) (ha : d5357 q = 1) (hb : d75630 q = 1) : d5357 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d75630 q = 1) (hb : d76827 q = 1) : d76493 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76827, d76493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d76827, d76493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d75630 q = 1) (hb : d76828 q = 1) : d76494 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76828, d76494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d76828, d76494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d75630 q = 1) (hb : d76829 q = 1) : d76495 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76829, d76495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d76829, d76495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d75630 q = 1) (hb : d76830 q = 1) : d76496 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76830, d76496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76830, d76496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro11041 (p : Pattern) (ha : d75630 p = 1) (hb : d76837 p = 1) : d76501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5942 q = 1) (hb : d70145 q = 1) : d5942 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5355 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5943 q = 1) (hb : d75629 q = 1) : d76491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5943, d75629, d76491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5943, d75629, d76491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d76826 q = 1) : d76492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76826, d76492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d75630, d76826, d76492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5357 q = 1) (hb : d75630 q = 1) : d5357 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d76827 q = 1) : d76493 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76827, d76493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76827, d76493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d76835 q = 1) : d76494 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76835, d76494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76835, d76494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d76836 q = 1) : d76495 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76836, d76495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76836, d76495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d76837 q = 1) : d76501 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76837, d76501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76837, d76501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11042 (p : Pattern) (ha : d75630 p = 1) (hb : d76847 p = 1) : d76512 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5968 q = 1) (hb : d70145 q = 1) : d5968 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5377 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5969 q = 1) (hb : d75629 q = 1) : d76507 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5969, d75629, d76507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5969, d75629, d76507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d76843 q = 1) : d76508 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76843, d76508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d75630, d76843, d76508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5379 q = 1) (hb : d75630 q = 1) : d5379 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d76844 q = 1) : d76509 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76844, d76509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76844, d76509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d76845 q = 1) : d76510 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76845, d76510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76845, d76510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d76846 q = 1) : d76511 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76846, d76511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76846, d76511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d76847 q = 1) : d76512 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76847, d76512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76847, d76512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11043 (p : Pattern) (ha : d75630 p = 1) (hb : d76853 p = 1) : d76518 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5896 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11036 q ha hb
  have h2 (q : Pattern) (ha : d5897 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5903 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11036 q ha hb
    | true =>
      simp only [d5903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11037 q ha hb
  have h4 (q : Pattern) (ha : d5904 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5905 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d5905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d76831 q = 1) : d76497 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76831, d76497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11039 q ha hb
    | true =>
      simp only [d76831, d76497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11040 q ha hb
  have h7 (q : Pattern) (ha : d5953 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11038 q ha hb
    | true =>
      simp only [d5953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11027 q ha hb
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d76832 q = 1) : d76498 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76832, d76498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76832, d76498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d76833 q = 1) : d76499 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76833, d76499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76833, d76499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d76834 q = 1) : d76500 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76834, d76500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d76834, d76500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75630 q = 1) (hb : d76838 q = 1) : d76502 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76838, d76502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76838, d76502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11041 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11034 q ha hb
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d76839 q = 1) : d76503 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76839, d76503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76839, d76503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75630 q = 1) (hb : d76840 q = 1) : d76504 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76840, d76504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76840, d76504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d76841 q = 1) : d76505 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76841, d76505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76841, d76505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d76842 q = 1) : d76506 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76842, d76506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76842, d76506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75630 q = 1) (hb : d76848 q = 1) : d76513 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76848, d76513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76848, d76513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11042 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11035 q ha hb
  have h19 (q : Pattern) (ha : d75630 q = 1) (hb : d76849 q = 1) : d76514 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76849, d76514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76849, d76514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d75630 q = 1) (hb : d76850 q = 1) : d76515 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76850, d76515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76850, d76515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d75630 q = 1) (hb : d76851 q = 1) : d76516 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76851, d76516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76851, d76516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d75630 q = 1) (hb : d76852 q = 1) : d76517 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76852, d76517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76852, d76517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d75630 q = 1) (hb : d76853 q = 1) : d76518 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76853, d76518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76853, d76518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro11044 (p : Pattern) (ha : d75630 p = 1) (hb : d76859 p = 1) : d76524 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d75630 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d76816 q = 1) : d76480 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76816, d76480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76816, d76480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11033 q ha hb
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d76817 q = 1) : d76481 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76817, d76481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76817, d76481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d76818 q = 1) : d76482 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76818, d76482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76818, d76482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d76819 q = 1) : d76483 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76819, d76483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76819, d76483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d76820 q = 1) : d76484 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76820, d76484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76820, d76484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d76854 q = 1) : d76519 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76854, d76519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76854, d76519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11043 q ha hb
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d76855 q = 1) : d76520 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76855, d76520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76855, d76520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d76856 q = 1) : d76521 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76856, d76521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76856, d76521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d76857 q = 1) : d76522 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76857, d76522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76857, d76522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75630 q = 1) (hb : d76858 q = 1) : d76523 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76858, d76523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76858, d76523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d75630 q = 1) (hb : d76859 q = 1) : d76524 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76859, d76524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76859, d76524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro11045 (p : Pattern) (ha : d644 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d633 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d634 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d634, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d635 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d636 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d637 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d639 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d640 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d640, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d641 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d642 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d643 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d644 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
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
theorem andIntro11046 (p : Pattern) (ha : d653 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d639 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d640 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d640, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d641 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d642 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d643 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d653 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
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
theorem andIntro11047 (p : Pattern) (ha : d736 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d731 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d732 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d732, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d733 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d734 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d735 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d736 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
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
theorem andIntro11048 (p : Pattern) (ha : d5997 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5992 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5993 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5993, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5993, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5994 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5995 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5996 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5997 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11049 (p : Pattern) (ha : d6005 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5992 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5993 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5993, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5993, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5994 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5995 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5996 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d6000 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6001 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6001, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6001, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d6002 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6003 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6004 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6005 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro11050 (p : Pattern) (ha : d6061 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6056 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6057 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6057, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6057, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6058 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6059 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6060 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d633 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d634 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d634, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d635 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d636 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d637 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6061 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro11051 (p : Pattern) (ha : d75630 p = 1) (hb : d76864 p = 1) : d76530 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6011 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6012 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6012, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6012, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6013 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6014 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6018 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6019 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6019, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6019, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d6020 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6024 q = 1) (hb : d70145 q = 1) : d6024 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d4830 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d6025 q = 1) (hb : d75629 q = 1) : d76525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6025, d75629, d76525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6025, d75629, d76525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d76860 q = 1) : d76526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76860, d76526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d75630, d76860, d76526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5401 q = 1) (hb : d75630 q = 1) : d5401 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d76861 q = 1) : d76527 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76861, d76527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76861, d76527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d76862 q = 1) : d76528 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76862, d76528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d76862, d76528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75630 q = 1) (hb : d76863 q = 1) : d76529 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76863, d76529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d76863, d76529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d75630 q = 1) (hb : d76864 q = 1) : d76530 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76864, d76530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76864, d76530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro11052 (p : Pattern) (ha : d75630 p = 1) (hb : d76869 p = 1) : d76536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6011 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6012 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6012, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6012, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6013 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6014 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6018 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6019 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6019, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6019, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d6020 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6024 q = 1) (hb : d70145 q = 1) : d6024 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d4830 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d6025 q = 1) (hb : d75629 q = 1) : d76525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6025, d75629, d76525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6025, d75629, d76525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d76860 q = 1) : d76526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76860, d76526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d75630, d76860, d76526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5401 q = 1) (hb : d75630 q = 1) : d5401 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d76861 q = 1) : d76527 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76861, d76527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76861, d76527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d76862 q = 1) : d76528 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76862, d76528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d76862, d76528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75630 q = 1) (hb : d76863 q = 1) : d76529 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76863, d76529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d76863, d76529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d6037 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d6038 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6038, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6038, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d6039 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d6039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d6040 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d6042 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d6043 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6043, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6043, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d6044 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d6044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d6045 q = 1) (hb : d70145 q = 1) : d6045 q = 1 := by
    exact ha
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d6046 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d6047 q = 1) (hb : d75629 q = 1) : d76531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6047, d75629, d76531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d6047, d75629, d76531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d75630 q = 1) (hb : d76865 q = 1) : d76532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76865, d76532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
    | true =>
      simp only [d75630, d76865, d76532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h29 (q : Pattern) (ha : d5408 q = 1) (hb : d75630 q = 1) : d5408 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d75630 q = 1) (hb : d76866 q = 1) : d76533 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76866, d76533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d76866, d76533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d75630 q = 1) (hb : d76867 q = 1) : d76534 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76867, d76534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d76867, d76534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d75630 q = 1) (hb : d76868 q = 1) : d76535 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76868, d76535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d76868, d76535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d75630 q = 1) (hb : d76869 q = 1) : d76536 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76869, d76536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76869, d76536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro11053 (p : Pattern) (ha : d75630 p = 1) (hb : d76876 p = 1) : d76541 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6045 q = 1) (hb : d70145 q = 1) : d6045 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6046 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6047 q = 1) (hb : d75629 q = 1) : d76531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6047, d75629, d76531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6047, d75629, d76531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d76865 q = 1) : d76532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76865, d76532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d75630, d76865, d76532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5408 q = 1) (hb : d75630 q = 1) : d5408 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d76866 q = 1) : d76533 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76866, d76533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76866, d76533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d76874 q = 1) : d76534 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76874, d76534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76874, d76534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d76875 q = 1) : d76535 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76875, d76535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76875, d76535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d76876 q = 1) : d76541 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76876, d76541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76876, d76541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11054 (p : Pattern) (ha : d75630 p = 1) (hb : d76886 p = 1) : d76552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6077 q = 1) (hb : d70145 q = 1) : d6077 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6090 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6091 q = 1) (hb : d75629 q = 1) : d76547 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6091, d75629, d76547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6091, d75629, d76547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d76882 q = 1) : d76548 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76882, d76548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d75630, d76882, d76548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5430 q = 1) (hb : d75630 q = 1) : d5430 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d76883 q = 1) : d76549 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76883, d76549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76883, d76549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d76884 q = 1) : d76550 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76884, d76550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76884, d76550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d76885 q = 1) : d76551 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76885, d76551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76885, d76551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d76886 q = 1) : d76552 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76886, d76552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76886, d76552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11055 (p : Pattern) (ha : d75630 p = 1) (hb : d76892 p = 1) : d76558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5998 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11048 q ha hb
  have h2 (q : Pattern) (ha : d5999 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6006 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11048 q ha hb
    | true =>
      simp only [d6006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11049 q ha hb
  have h4 (q : Pattern) (ha : d6007 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6008 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d76870 q = 1) : d76537 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76870, d76537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11051 q ha hb
    | true =>
      simp only [d76870, d76537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11052 q ha hb
  have h7 (q : Pattern) (ha : d6062 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11050 q ha hb
    | true =>
      simp only [d6062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11045 q ha hb
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d76871 q = 1) : d76538 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76871, d76538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76871, d76538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d76872 q = 1) : d76539 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76872, d76539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76872, d76539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d76873 q = 1) : d76540 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76873, d76540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d76873, d76540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75630 q = 1) (hb : d76877 q = 1) : d76542 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76877, d76542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76877, d76542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11053 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11046 q ha hb
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d76878 q = 1) : d76543 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76878, d76543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76878, d76543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75630 q = 1) (hb : d76879 q = 1) : d76544 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76879, d76544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76879, d76544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d76880 q = 1) : d76545 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76880, d76545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76880, d76545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d76881 q = 1) : d76546 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76881, d76546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76881, d76546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75630 q = 1) (hb : d76887 q = 1) : d76553 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76887, d76553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76887, d76553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11054 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11047 q ha hb
  have h19 (q : Pattern) (ha : d75630 q = 1) (hb : d76888 q = 1) : d76554 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76888, d76554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76888, d76554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d75630 q = 1) (hb : d76889 q = 1) : d76555 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76889, d76555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76889, d76555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d75630 q = 1) (hb : d76890 q = 1) : d76556 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76890, d76556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76890, d76556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d75630 q = 1) (hb : d76891 q = 1) : d76557 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76891, d76557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76891, d76557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d75630 q = 1) (hb : d76892 q = 1) : d76558 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76892, d76558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76892, d76558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro11056 (p : Pattern) (ha : d75630 p = 1) (hb : d76898 p = 1) : d76564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d76893 q = 1) : d76559 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76893, d76559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76893, d76559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11055 q ha hb
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d76894 q = 1) : d76560 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76894, d76560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76894, d76560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d76895 q = 1) : d76561 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76895, d76561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76895, d76561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d76896 q = 1) : d76562 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76896, d76562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76896, d76562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d76897 q = 1) : d76563 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76897, d76563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76897, d76563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d76898 q = 1) : d76564 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76898, d76564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76898, d76564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11057 (p : Pattern) (ha : d950 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d939 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d940 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d940, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d941 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d942 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d943 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d945 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d946 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d946, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d947 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d948 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d949 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d950 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
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
theorem andIntro11058 (p : Pattern) (ha : d959 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d945 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d946 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d946, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d947 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d948 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d949 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d959 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
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
theorem andIntro11059 (p : Pattern) (ha : d1069 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1064 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1065 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1065, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1066 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1067 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1068 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1069 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
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
theorem andIntro11060 (p : Pattern) (ha : d6124 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6119 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6120 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6120, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6120, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6121 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6122 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6123 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6124 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11061 (p : Pattern) (ha : d6133 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6119 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6120 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6120, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6120, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6121 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6122 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6123 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d6128 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6129 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6129, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6129, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d6130 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6131 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6132 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6133 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro11062 (p : Pattern) (ha : d6193 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6188 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6189 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6189, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6189, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6190 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6191 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6192 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d939 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d940 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d940, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d941 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d942 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d943 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6193 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro11063 (p : Pattern) (ha : d75630 p = 1) (hb : d76904 p = 1) : d76571 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6139 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6140 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6140, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6140, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6141 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6142 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6146 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6147 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6147, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6147, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d6148 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6152 q = 1) (hb : d70145 q = 1) : d6152 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d4925 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d6153 q = 1) (hb : d75629 q = 1) : d76566 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6153, d75629, d76566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6153, d75629, d76566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d76900 q = 1) : d76567 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76900, d76567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d75630, d76900, d76567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6161 q = 1) (hb : d75630 q = 1) : d6161 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d76901 q = 1) : d76568 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76901, d76568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76901, d76568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d76902 q = 1) : d76569 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76902, d76569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d76902, d76569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75630 q = 1) (hb : d76903 q = 1) : d76570 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76903, d76570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d76903, d76570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d75630 q = 1) (hb : d76904 q = 1) : d76571 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76904, d76571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76904, d76571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro11064 (p : Pattern) (ha : d75630 p = 1) (hb : d76909 p = 1) : d76577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6139 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6140 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6140, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6140, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6141 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6142 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6146 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6147 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6147, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6147, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d6148 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6152 q = 1) (hb : d70145 q = 1) : d6152 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d4925 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d6153 q = 1) (hb : d75629 q = 1) : d76566 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6153, d75629, d76566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6153, d75629, d76566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d76900 q = 1) : d76567 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76900, d76567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d75630, d76900, d76567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6161 q = 1) (hb : d75630 q = 1) : d6161 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d76901 q = 1) : d76568 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76901, d76568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76901, d76568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d76902 q = 1) : d76569 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76902, d76569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d76902, d76569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75630 q = 1) (hb : d76903 q = 1) : d76570 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76903, d76570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d76903, d76570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d6167 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d6168 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6168, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6168, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d6169 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d6169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d6170 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d6172 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d6173 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6173, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6173, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d6174 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d6174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d6175 q = 1) (hb : d70145 q = 1) : d6175 q = 1 := by
    exact ha
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d6176 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d6177 q = 1) (hb : d75629 q = 1) : d76572 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6177, d75629, d76572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d6177, d75629, d76572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d75630 q = 1) (hb : d76905 q = 1) : d76573 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76905, d76573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
    | true =>
      simp only [d75630, d76905, d76573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h29 (q : Pattern) (ha : d6182 q = 1) (hb : d75630 q = 1) : d6182 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d75630 q = 1) (hb : d76906 q = 1) : d76574 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76906, d76574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d76906, d76574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d75630 q = 1) (hb : d76907 q = 1) : d76575 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76907, d76575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d76907, d76575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d75630 q = 1) (hb : d76908 q = 1) : d76576 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76908, d76576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d76908, d76576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d75630 q = 1) (hb : d76909 q = 1) : d76577 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76909, d76577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76909, d76577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro11065 (p : Pattern) (ha : d75630 p = 1) (hb : d76916 p = 1) : d76582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6175 q = 1) (hb : d70145 q = 1) : d6175 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6176 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6177 q = 1) (hb : d75629 q = 1) : d76572 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6177, d75629, d76572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6177, d75629, d76572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d76905 q = 1) : d76573 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76905, d76573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d75630, d76905, d76573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6182 q = 1) (hb : d75630 q = 1) : d6182 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d76906 q = 1) : d76574 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76906, d76574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76906, d76574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d76914 q = 1) : d76575 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76914, d76575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76914, d76575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d76915 q = 1) : d76576 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76915, d76576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76915, d76576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d76916 q = 1) : d76582 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76916, d76582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76916, d76582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11066 (p : Pattern) (ha : d75630 p = 1) (hb : d76926 p = 1) : d76593 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6209 q = 1) (hb : d70145 q = 1) : d6209 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6222 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6223 q = 1) (hb : d75629 q = 1) : d76588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6223, d75629, d76588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6223, d75629, d76588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d76922 q = 1) : d76589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76922, d76589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d75630, d76922, d76589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6235 q = 1) (hb : d75630 q = 1) : d6235 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d76923 q = 1) : d76590 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76923, d76590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76923, d76590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d76924 q = 1) : d76591 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76924, d76591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76924, d76591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d76925 q = 1) : d76592 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76925, d76592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76925, d76592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d76926 q = 1) : d76593 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76926, d76593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76926, d76593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11067 (p : Pattern) (ha : d75630 p = 1) (hb : d76932 p = 1) : d76599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6125 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11060 q ha hb
  have h2 (q : Pattern) (ha : d6126 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6134 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11060 q ha hb
    | true =>
      simp only [d6134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11061 q ha hb
  have h4 (q : Pattern) (ha : d6135 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6136 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d76910 q = 1) : d76578 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76910, d76578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11063 q ha hb
    | true =>
      simp only [d76910, d76578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11064 q ha hb
  have h7 (q : Pattern) (ha : d6194 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11062 q ha hb
    | true =>
      simp only [d6194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11057 q ha hb
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d76911 q = 1) : d76579 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76911, d76579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76911, d76579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d76912 q = 1) : d76580 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76912, d76580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76912, d76580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d76913 q = 1) : d76581 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76913, d76581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d76913, d76581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75630 q = 1) (hb : d76917 q = 1) : d76583 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76917, d76583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76917, d76583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11065 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11058 q ha hb
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d76918 q = 1) : d76584 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76918, d76584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76918, d76584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75630 q = 1) (hb : d76919 q = 1) : d76585 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76919, d76585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76919, d76585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d76920 q = 1) : d76586 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76920, d76586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76920, d76586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d76921 q = 1) : d76587 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76921, d76587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76921, d76587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75630 q = 1) (hb : d76927 q = 1) : d76594 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76927, d76594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76927, d76594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11066 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11059 q ha hb
  have h19 (q : Pattern) (ha : d75630 q = 1) (hb : d76928 q = 1) : d76595 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76928, d76595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76928, d76595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d75630 q = 1) (hb : d76929 q = 1) : d76596 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76929, d76596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76929, d76596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d75630 q = 1) (hb : d76930 q = 1) : d76597 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76930, d76597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76930, d76597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d75630 q = 1) (hb : d76931 q = 1) : d76598 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76931, d76598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76931, d76598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d75630 q = 1) (hb : d76932 q = 1) : d76599 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76932, d76599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76932, d76599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro11068 (p : Pattern) (ha : d75630 p = 1) (hb : d76938 p = 1) : d76605 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d76933 q = 1) : d76600 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76933, d76600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76933, d76600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11067 q ha hb
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d76934 q = 1) : d76601 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76934, d76601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76934, d76601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d76935 q = 1) : d76602 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76935, d76602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76935, d76602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d76936 q = 1) : d76603 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76936, d76603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76936, d76603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d76937 q = 1) : d76604 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76937, d76604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76937, d76604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d76938 q = 1) : d76605 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76938, d76605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76938, d76605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11069 (p : Pattern) (ha : d1361 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1350 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1351 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1351, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1352 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1353 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1354 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1356 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1357 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1357, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1358 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1359 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1360 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1361 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
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
theorem andIntro11070 (p : Pattern) (ha : d1370 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1356 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1357 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1357, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1358 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1359 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1360 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1370 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
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
theorem andIntro11071 (p : Pattern) (ha : d1503 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1498 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1499 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1499, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1499, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1500 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1501 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1502 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1503 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
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
theorem andIntro11072 (p : Pattern) (ha : d6263 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6258 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6259 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6259, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6259, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6260 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6261 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6262 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6263 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11073 (p : Pattern) (ha : d6272 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6258 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6259 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6259, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6259, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6260 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6261 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6262 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d6267 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6268 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6268, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6268, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d6269 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6270 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6271 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6272 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro11074 (p : Pattern) (ha : d6332 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6327 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6328 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6328, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6328, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6329 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6330 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6331 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1350 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1351 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1351, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1352 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1353 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1354 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6332 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro11075 (p : Pattern) (ha : d75630 p = 1) (hb : d76945 p = 1) : d76613 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6278 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6279 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6279, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6279, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6280 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6281 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6285 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6286 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6286, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6286, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d6287 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6291 q = 1) (hb : d70145 q = 1) : d6291 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5035 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d6292 q = 1) (hb : d75629 q = 1) : d76608 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6292, d75629, d76608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6292, d75629, d76608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d76941 q = 1) : d76609 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76941, d76609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d75630, d76941, d76609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6300 q = 1) (hb : d75630 q = 1) : d6300 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d76942 q = 1) : d76610 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76942, d76610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76942, d76610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d76943 q = 1) : d76611 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76943, d76611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d76943, d76611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75630 q = 1) (hb : d76944 q = 1) : d76612 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76944, d76612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d76944, d76612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d75630 q = 1) (hb : d76945 q = 1) : d76613 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76945, d76613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76945, d76613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro11076 (p : Pattern) (ha : d75630 p = 1) (hb : d76950 p = 1) : d76619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6278 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6279 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6279, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6279, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6280 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6281 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6285 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6286 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6286, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6286, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d6287 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6291 q = 1) (hb : d70145 q = 1) : d6291 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5035 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d6292 q = 1) (hb : d75629 q = 1) : d76608 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6292, d75629, d76608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6292, d75629, d76608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d76941 q = 1) : d76609 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76941, d76609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d75630, d76941, d76609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6300 q = 1) (hb : d75630 q = 1) : d6300 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d76942 q = 1) : d76610 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76942, d76610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76942, d76610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d76943 q = 1) : d76611 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76943, d76611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d76943, d76611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75630 q = 1) (hb : d76944 q = 1) : d76612 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76944, d76612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d76944, d76612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d6306 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d6307 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6307, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6307, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d6308 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d6308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d6309 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d6311 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d6312 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6312, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6312, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d6313 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d6313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d6314 q = 1) (hb : d70145 q = 1) : d6314 q = 1 := by
    exact ha
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d6315 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d6316 q = 1) (hb : d75629 q = 1) : d76614 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6316, d75629, d76614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d6316, d75629, d76614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d75630 q = 1) (hb : d76946 q = 1) : d76615 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76946, d76615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
    | true =>
      simp only [d75630, d76946, d76615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h29 (q : Pattern) (ha : d6321 q = 1) (hb : d75630 q = 1) : d6321 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d75630 q = 1) (hb : d76947 q = 1) : d76616 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76947, d76616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d76947, d76616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d75630 q = 1) (hb : d76948 q = 1) : d76617 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76948, d76617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d76948, d76617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d75630 q = 1) (hb : d76949 q = 1) : d76618 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76949, d76618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d76949, d76618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d75630 q = 1) (hb : d76950 q = 1) : d76619 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76950, d76619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76950, d76619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro11077 (p : Pattern) (ha : d75630 p = 1) (hb : d76957 p = 1) : d76624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6314 q = 1) (hb : d70145 q = 1) : d6314 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6315 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6316 q = 1) (hb : d75629 q = 1) : d76614 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6316, d75629, d76614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6316, d75629, d76614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d76946 q = 1) : d76615 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76946, d76615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d75630, d76946, d76615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6321 q = 1) (hb : d75630 q = 1) : d6321 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d76947 q = 1) : d76616 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76947, d76616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76947, d76616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d76955 q = 1) : d76617 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76955, d76617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76955, d76617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d76956 q = 1) : d76618 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76956, d76618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76956, d76618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d76957 q = 1) : d76624 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76957, d76624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76957, d76624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11078 (p : Pattern) (ha : d75630 p = 1) (hb : d76967 p = 1) : d76635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6348 q = 1) (hb : d70145 q = 1) : d6348 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6367 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6368 q = 1) (hb : d75629 q = 1) : d76630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6368, d75629, d76630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6368, d75629, d76630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d76963 q = 1) : d76631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76963, d76631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d75630, d76963, d76631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6380 q = 1) (hb : d75630 q = 1) : d6380 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d76964 q = 1) : d76632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76964, d76632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76964, d76632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d76965 q = 1) : d76633 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76965, d76633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76965, d76633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d76966 q = 1) : d76634 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76966, d76634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76966, d76634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d76967 q = 1) : d76635 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76967, d76635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76967, d76635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11079 (p : Pattern) (ha : d75630 p = 1) (hb : d76973 p = 1) : d76641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6264 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11072 q ha hb
  have h2 (q : Pattern) (ha : d6265 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6273 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11072 q ha hb
    | true =>
      simp only [d6273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11073 q ha hb
  have h4 (q : Pattern) (ha : d6274 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6275 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d76951 q = 1) : d76620 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76951, d76620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11075 q ha hb
    | true =>
      simp only [d76951, d76620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11076 q ha hb
  have h7 (q : Pattern) (ha : d6333 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11074 q ha hb
    | true =>
      simp only [d6333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11069 q ha hb
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d76952 q = 1) : d76621 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76952, d76621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76952, d76621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d76953 q = 1) : d76622 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76953, d76622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76953, d76622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d76954 q = 1) : d76623 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76954, d76623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d76954, d76623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75630 q = 1) (hb : d76958 q = 1) : d76625 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76958, d76625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76958, d76625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11077 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11070 q ha hb
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d76959 q = 1) : d76626 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76959, d76626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76959, d76626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75630 q = 1) (hb : d76960 q = 1) : d76627 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76960, d76627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76960, d76627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d76961 q = 1) : d76628 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76961, d76628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76961, d76628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d76962 q = 1) : d76629 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76962, d76629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76962, d76629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75630 q = 1) (hb : d76968 q = 1) : d76636 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76968, d76636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76968, d76636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11078 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11071 q ha hb
  have h19 (q : Pattern) (ha : d75630 q = 1) (hb : d76969 q = 1) : d76637 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76969, d76637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76969, d76637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d75630 q = 1) (hb : d76970 q = 1) : d76638 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76970, d76638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76970, d76638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d75630 q = 1) (hb : d76971 q = 1) : d76639 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76971, d76639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76971, d76639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d75630 q = 1) (hb : d76972 q = 1) : d76640 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76972, d76640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76972, d76640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d75630 q = 1) (hb : d76973 q = 1) : d76641 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76973, d76641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76973, d76641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro11080 (p : Pattern) (ha : d75630 p = 1) (hb : d76979 p = 1) : d76647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d76974 q = 1) : d76642 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76974, d76642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76974, d76642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11079 q ha hb
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d76975 q = 1) : d76643 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76975, d76643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76975, d76643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d76976 q = 1) : d76644 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76976, d76644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76976, d76644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d76977 q = 1) : d76645 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76977, d76645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76977, d76645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d76978 q = 1) : d76646 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76978, d76646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76978, d76646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d76979 q = 1) : d76647 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76979, d76647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76979, d76647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11081 (p : Pattern) (ha : d1838 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1827 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1828 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1828, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1829 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1830 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1831 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1833 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1834 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1834, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1835 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1836 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1837 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1838 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro11082 (p : Pattern) (ha : d1847 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1833 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1834 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1834, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1835 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1836 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1837 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1847 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11083 (p : Pattern) (ha : d1980 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1975 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1976 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1976, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1976, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1977 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1978 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1979 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1980 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11084 (p : Pattern) (ha : d6409 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6404 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6405 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6405, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6405, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6406 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6407 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6408 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6409 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11085 (p : Pattern) (ha : d6418 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6404 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6405 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6405, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6405, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6406 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6407 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6408 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d6413 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6414 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6414, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6414, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d6415 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6416 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6417 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6418 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro11086 (p : Pattern) (ha : d6478 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6473 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6474 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6474, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6474, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6475 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6476 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6477 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1827 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1828 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1828, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1829 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1830 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1831 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6478 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro11087 (p : Pattern) (ha : d75630 p = 1) (hb : d76987 p = 1) : d76656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6424 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6425 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6425, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6425, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6426 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6427 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6431 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6432 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6432, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6432, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d6433 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6437 q = 1) (hb : d70145 q = 1) : d6437 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5151 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d6438 q = 1) (hb : d75629 q = 1) : d76651 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6438, d75629, d76651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6438, d75629, d76651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d76983 q = 1) : d76652 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76983, d76652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d75630, d76983, d76652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6446 q = 1) (hb : d75630 q = 1) : d6446 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d76984 q = 1) : d76653 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76984, d76653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76984, d76653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d76985 q = 1) : d76654 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76985, d76654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d76985, d76654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75630 q = 1) (hb : d76986 q = 1) : d76655 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76986, d76655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d76986, d76655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d75630 q = 1) (hb : d76987 q = 1) : d76656 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76987, d76656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76987, d76656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro11088 (p : Pattern) (ha : d75630 p = 1) (hb : d76992 p = 1) : d76662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6424 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6425 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6425, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6425, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6426 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6427 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6431 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6432 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6432, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6432, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d6433 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6437 q = 1) (hb : d70145 q = 1) : d6437 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5151 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d6438 q = 1) (hb : d75629 q = 1) : d76651 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6438, d75629, d76651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6438, d75629, d76651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d76983 q = 1) : d76652 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76983, d76652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d75630, d76983, d76652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6446 q = 1) (hb : d75630 q = 1) : d6446 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d76984 q = 1) : d76653 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76984, d76653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76984, d76653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d76985 q = 1) : d76654 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76985, d76654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d76985, d76654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75630 q = 1) (hb : d76986 q = 1) : d76655 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76986, d76655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d76986, d76655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d6452 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d6453 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6453, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6453, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d6454 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d6454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d6455 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d6457 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d6458 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6458, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6458, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d6459 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d6459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d6460 q = 1) (hb : d70145 q = 1) : d6460 q = 1 := by
    exact ha
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d6461 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d6462 q = 1) (hb : d75629 q = 1) : d76657 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6462, d75629, d76657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d6462, d75629, d76657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d75630 q = 1) (hb : d76988 q = 1) : d76658 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76988, d76658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
    | true =>
      simp only [d75630, d76988, d76658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h29 (q : Pattern) (ha : d6467 q = 1) (hb : d75630 q = 1) : d6467 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d75630 q = 1) (hb : d76989 q = 1) : d76659 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76989, d76659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d76989, d76659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d75630 q = 1) (hb : d76990 q = 1) : d76660 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76990, d76660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d76990, d76660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d75630 q = 1) (hb : d76991 q = 1) : d76661 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76991, d76661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d76991, d76661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d75630 q = 1) (hb : d76992 q = 1) : d76662 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76992, d76662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76992, d76662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro11089 (p : Pattern) (ha : d75630 p = 1) (hb : d76999 p = 1) : d76667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6460 q = 1) (hb : d70145 q = 1) : d6460 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6461 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6462 q = 1) (hb : d75629 q = 1) : d76657 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6462, d75629, d76657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6462, d75629, d76657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d76988 q = 1) : d76658 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d76988, d76658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d75630, d76988, d76658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6467 q = 1) (hb : d75630 q = 1) : d6467 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d76989 q = 1) : d76659 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76989, d76659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76989, d76659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d76997 q = 1) : d76660 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76997, d76660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76997, d76660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d76998 q = 1) : d76661 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76998, d76661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76998, d76661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d76999 q = 1) : d76667 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76999, d76667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76999, d76667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11090 (p : Pattern) (ha : d75630 p = 1) (hb : d77009 p = 1) : d76678 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6494 q = 1) (hb : d70145 q = 1) : d6494 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6513 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6514 q = 1) (hb : d75629 q = 1) : d76673 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6514, d75629, d76673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6514, d75629, d76673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d77005 q = 1) : d76674 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d77005, d76674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d75630, d77005, d76674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6526 q = 1) (hb : d75630 q = 1) : d6526 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d77006 q = 1) : d76675 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77006, d76675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77006, d76675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d77007 q = 1) : d76676 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77007, d76676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77007, d76676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d77008 q = 1) : d76677 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77008, d76677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77008, d76677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d77009 q = 1) : d76678 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77009, d76678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77009, d76678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11091 (p : Pattern) (ha : d75630 p = 1) (hb : d77015 p = 1) : d76684 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6410 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11084 q ha hb
  have h2 (q : Pattern) (ha : d6411 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6419 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11084 q ha hb
    | true =>
      simp only [d6419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11085 q ha hb
  have h4 (q : Pattern) (ha : d6420 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6421 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d76993 q = 1) : d76663 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76993, d76663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11087 q ha hb
    | true =>
      simp only [d76993, d76663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11088 q ha hb
  have h7 (q : Pattern) (ha : d6479 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11086 q ha hb
    | true =>
      simp only [d6479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11081 q ha hb
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d76994 q = 1) : d76664 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76994, d76664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76994, d76664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d76995 q = 1) : d76665 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76995, d76665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76995, d76665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d76996 q = 1) : d76666 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76996, d76666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d76996, d76666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75630 q = 1) (hb : d77000 q = 1) : d76668 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77000, d76668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77000, d76668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11089 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11082 q ha hb
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d77001 q = 1) : d76669 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77001, d76669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77001, d76669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75630 q = 1) (hb : d77002 q = 1) : d76670 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77002, d76670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77002, d76670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d77003 q = 1) : d76671 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77003, d76671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d77003, d76671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d77004 q = 1) : d76672 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77004, d76672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77004, d76672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75630 q = 1) (hb : d77010 q = 1) : d76679 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77010, d76679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77010, d76679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11090 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11083 q ha hb
  have h19 (q : Pattern) (ha : d75630 q = 1) (hb : d77011 q = 1) : d76680 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77011, d76680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77011, d76680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d75630 q = 1) (hb : d77012 q = 1) : d76681 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77012, d76681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d77012, d76681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d75630 q = 1) (hb : d77013 q = 1) : d76682 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77013, d76682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d77013, d76682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d75630 q = 1) (hb : d77014 q = 1) : d76683 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77014, d76683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d77014, d76683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d75630 q = 1) (hb : d77015 q = 1) : d76684 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77015, d76684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77015, d76684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro11092 (p : Pattern) (ha : d75630 p = 1) (hb : d77021 p = 1) : d76690 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d77016 q = 1) : d76685 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77016, d76685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77016, d76685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11091 q ha hb
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d77017 q = 1) : d76686 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77017, d76686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77017, d76686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d77018 q = 1) : d76687 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77018, d76687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77018, d76687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d77019 q = 1) : d76688 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77019, d76688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77019, d76688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d77020 q = 1) : d76689 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77020, d76689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77020, d76689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d77021 q = 1) : d76690 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77021, d76690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77021, d76690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11093 (p : Pattern) (ha : d2316 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2305 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2306 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2306, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2307 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2308 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2309 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2311 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2312 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2312, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2313 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2314 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2315 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2316 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro11094 (p : Pattern) (ha : d2325 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2312 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2312, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2313 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2314 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2315 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2325 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11095 (p : Pattern) (ha : d2458 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2453 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2454 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2454, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2454, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2455 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2456 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2457 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2458 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11096 (p : Pattern) (ha : d6556 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6551 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6552 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6552, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6552, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6553 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6554 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6555 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6556 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11097 (p : Pattern) (ha : d6565 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6551 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6552 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6552, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6552, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6553 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6554 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6555 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d6560 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6561 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6561, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6561, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d6562 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6563 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6564 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6565 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro11098 (p : Pattern) (ha : d6625 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6620 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6621 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6621, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6621, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6622 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6623 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6624 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2305 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2306 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2306, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2307 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2308 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2309 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6625 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro11099 (p : Pattern) (ha : d75630 p = 1) (hb : d77030 p = 1) : d76700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6571 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6572 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6572, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6572, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6573 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6574 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6578 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6579 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6579, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6579, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d6580 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6584 q = 1) (hb : d70145 q = 1) : d6584 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5264 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d6585 q = 1) (hb : d75629 q = 1) : d76695 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6585, d75629, d76695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6585, d75629, d76695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d77026 q = 1) : d76696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d77026, d76696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d75630, d77026, d76696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6593 q = 1) (hb : d75630 q = 1) : d6593 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d77027 q = 1) : d76697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77027, d76697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77027, d76697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d77028 q = 1) : d76698 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77028, d76698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d77028, d76698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75630 q = 1) (hb : d77029 q = 1) : d76699 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77029, d76699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d77029, d76699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d75630 q = 1) (hb : d77030 q = 1) : d76700 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77030, d76700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77030, d76700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro11100 (p : Pattern) (ha : d75630 p = 1) (hb : d77035 p = 1) : d76706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6571 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6572 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6572, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6572, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6573 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6574 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6578 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6579 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6579, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6579, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d6580 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6584 q = 1) (hb : d70145 q = 1) : d6584 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5264 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d6585 q = 1) (hb : d75629 q = 1) : d76695 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6585, d75629, d76695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6585, d75629, d76695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d77026 q = 1) : d76696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d77026, d76696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d75630, d77026, d76696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6593 q = 1) (hb : d75630 q = 1) : d6593 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d77027 q = 1) : d76697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77027, d76697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77027, d76697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d77028 q = 1) : d76698 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77028, d76698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d77028, d76698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75630 q = 1) (hb : d77029 q = 1) : d76699 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77029, d76699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d77029, d76699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d6599 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d6600 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6600, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6600, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d6601 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d6601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d6602 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d6604 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d6605 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6605, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6605, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d6606 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d6606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d6607 q = 1) (hb : d70145 q = 1) : d6607 q = 1 := by
    exact ha
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d6608 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d6609 q = 1) (hb : d75629 q = 1) : d76701 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6609, d75629, d76701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d6609, d75629, d76701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d75630 q = 1) (hb : d77031 q = 1) : d76702 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d77031, d76702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
    | true =>
      simp only [d75630, d77031, d76702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h29 (q : Pattern) (ha : d6614 q = 1) (hb : d75630 q = 1) : d6614 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d75630 q = 1) (hb : d77032 q = 1) : d76703 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77032, d76703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d77032, d76703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d75630 q = 1) (hb : d77033 q = 1) : d76704 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77033, d76704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d77033, d76704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d75630 q = 1) (hb : d77034 q = 1) : d76705 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77034, d76705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d77034, d76705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d75630 q = 1) (hb : d77035 q = 1) : d76706 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77035, d76706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77035, d76706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro11101 (p : Pattern) (ha : d75630 p = 1) (hb : d77042 p = 1) : d76711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6607 q = 1) (hb : d70145 q = 1) : d6607 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6608 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6609 q = 1) (hb : d75629 q = 1) : d76701 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6609, d75629, d76701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6609, d75629, d76701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d77031 q = 1) : d76702 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d77031, d76702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d75630, d77031, d76702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6614 q = 1) (hb : d75630 q = 1) : d6614 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d77032 q = 1) : d76703 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77032, d76703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77032, d76703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d77040 q = 1) : d76704 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77040, d76704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77040, d76704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d77041 q = 1) : d76705 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77041, d76705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77041, d76705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d77042 q = 1) : d76711 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77042, d76711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77042, d76711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11102 (p : Pattern) (ha : d75630 p = 1) (hb : d77052 p = 1) : d76722 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6641 q = 1) (hb : d70145 q = 1) : d6641 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6660 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6661 q = 1) (hb : d75629 q = 1) : d76717 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6661, d75629, d76717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6661, d75629, d76717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d77048 q = 1) : d76718 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d77048, d76718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d75630, d77048, d76718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6673 q = 1) (hb : d75630 q = 1) : d6673 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d77049 q = 1) : d76719 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77049, d76719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77049, d76719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d77050 q = 1) : d76720 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77050, d76720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77050, d76720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d77051 q = 1) : d76721 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77051, d76721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77051, d76721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d77052 q = 1) : d76722 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77052, d76722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77052, d76722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11103 (p : Pattern) (ha : d75630 p = 1) (hb : d77058 p = 1) : d76728 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6557 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11096 q ha hb
  have h2 (q : Pattern) (ha : d6558 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6566 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11096 q ha hb
    | true =>
      simp only [d6566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11097 q ha hb
  have h4 (q : Pattern) (ha : d6567 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6568 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d77036 q = 1) : d76707 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77036, d76707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11099 q ha hb
    | true =>
      simp only [d77036, d76707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11100 q ha hb
  have h7 (q : Pattern) (ha : d6626 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11098 q ha hb
    | true =>
      simp only [d6626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11093 q ha hb
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d77037 q = 1) : d76708 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77037, d76708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77037, d76708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d77038 q = 1) : d76709 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77038, d76709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d77038, d76709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d77039 q = 1) : d76710 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77039, d76710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d77039, d76710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75630 q = 1) (hb : d77043 q = 1) : d76712 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77043, d76712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77043, d76712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11101 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11094 q ha hb
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d77044 q = 1) : d76713 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77044, d76713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77044, d76713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75630 q = 1) (hb : d77045 q = 1) : d76714 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77045, d76714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77045, d76714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d77046 q = 1) : d76715 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77046, d76715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d77046, d76715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d77047 q = 1) : d76716 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77047, d76716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77047, d76716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75630 q = 1) (hb : d77053 q = 1) : d76723 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77053, d76723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77053, d76723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11102 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11095 q ha hb
  have h19 (q : Pattern) (ha : d75630 q = 1) (hb : d77054 q = 1) : d76724 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77054, d76724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77054, d76724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d75630 q = 1) (hb : d77055 q = 1) : d76725 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77055, d76725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d77055, d76725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d75630 q = 1) (hb : d77056 q = 1) : d76726 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77056, d76726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d77056, d76726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d75630 q = 1) (hb : d77057 q = 1) : d76727 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77057, d76727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d77057, d76727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d75630 q = 1) (hb : d77058 q = 1) : d76728 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77058, d76728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77058, d76728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro11104 (p : Pattern) (ha : d75630 p = 1) (hb : d77064 p = 1) : d76734 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d77059 q = 1) : d76729 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77059, d76729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77059, d76729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11103 q ha hb
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d77060 q = 1) : d76730 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77060, d76730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77060, d76730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d77061 q = 1) : d76731 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77061, d76731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77061, d76731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d77062 q = 1) : d76732 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77062, d76732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77062, d76732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d77063 q = 1) : d76733 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77063, d76733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77063, d76733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d77064 q = 1) : d76734 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77064, d76734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d77064, d76734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11105 (p : Pattern) (ha : d75630 p = 1) (hb : d77070 p = 1) : d76740 p = 1 := by
  have h0 (q : Pattern) (ha : d75630 q = 1) (hb : d76899 q = 1) : d76565 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76899, d76565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11044 q ha hb
    | true =>
      simp only [d76899, d76565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11056 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d76939 q = 1) : d76606 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76939, d76606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76939, d76606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11068 q ha hb
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d76940 q = 1) : d76607 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76940, d76607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76940, d76607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d76980 q = 1) : d76648 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76980, d76648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76980, d76648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11080 q ha hb
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d76981 q = 1) : d76649 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76981, d76649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76981, d76649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d76982 q = 1) : d76650 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d76982, d76650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76982, d76650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d77022 q = 1) : d76691 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77022, d76691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d77022, d76691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11092 q ha hb
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d77023 q = 1) : d76692 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77023, d76692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d77023, d76692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d77024 q = 1) : d76693 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77024, d76693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d77024, d76693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d77025 q = 1) : d76694 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d77025, d76694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77025, d76694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75630 q = 1) (hb : d77065 q = 1) : d76735 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77065, d76735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d77065, d76735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11104 q ha hb
  have h12 (q : Pattern) (ha : d75630 q = 1) (hb : d77066 q = 1) : d76736 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77066, d76736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d77066, d76736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d77067 q = 1) : d76737 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77067, d76737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d77067, d76737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d75630 q = 1) (hb : d77068 q = 1) : d76738 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d77068, d76738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d77068, d76738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d77069 q = 1) : d76739 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d77069, d76739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77069, d76739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d77070 q = 1) : d76740 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d77070, d76740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77070, d76740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro11106 (p : Pattern) (ha : d75630 p = 1) (hb : d77076 p = 1) : d76746 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d77071 q = 1) : d76741 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d77071, d76741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11105 q ha hb
    | true =>
      simp only [d77071, d76741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d77072 q = 1) : d76742 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d77072, d76742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77072, d76742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d77073 q = 1) : d76743 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d77073, d76743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77073, d76743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d77074 q = 1) : d76744 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d77074, d76744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77074, d76744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d77075 q = 1) : d76745 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d77075, d76745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77075, d76745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d77076 q = 1) : d76746 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d77076, d76746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77076, d76746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11107 (p : Pattern) (ha : d75630 p = 1) (hb : d77082 p = 1) : d76752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d77077 q = 1) : d76747 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d77077, d76747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11106 q ha hb
    | true =>
      simp only [d77077, d76747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d77078 q = 1) : d76748 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d77078, d76748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77078, d76748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d77079 q = 1) : d76749 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d77079, d76749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77079, d76749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d77080 q = 1) : d76750 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d77080, d76750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77080, d76750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d77081 q = 1) : d76751 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d77081, d76751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77081, d76751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d77082 q = 1) : d76752 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d77082, d76752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77082, d76752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11108 (p : Pattern) (ha : d75630 p = 1) (hb : d77088 p = 1) : d76758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d77083 q = 1) : d76753 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d77083, d76753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11107 q ha hb
    | true =>
      simp only [d77083, d76753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d77084 q = 1) : d76754 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d77084, d76754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77084, d76754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d77085 q = 1) : d76755 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d77085, d76755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77085, d76755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d77086 q = 1) : d76756 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d77086, d76756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77086, d76756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d77087 q = 1) : d76757 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d77087, d76757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77087, d76757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d77088 q = 1) : d76758 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d77088, d76758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77088, d76758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11109 (p : Pattern) (ha : d75630 p = 1) (hb : d77094 p = 1) : d76764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d77089 q = 1) : d76759 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d77089, d76759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11108 q ha hb
    | true =>
      simp only [d77089, d76759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d77090 q = 1) : d76760 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d77090, d76760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77090, d76760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d77091 q = 1) : d76761 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d77091, d76761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77091, d76761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d77092 q = 1) : d76762 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d77092, d76762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77092, d76762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d77093 q = 1) : d76763 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d77093, d76763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77093, d76763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d77094 q = 1) : d76764 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d77094, d76764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77094, d76764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11110 (p : Pattern) (ha : d75630 p = 1) (hb : d77100 p = 1) : d76770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d77095 q = 1) : d76765 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d77095, d76765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11109 q ha hb
    | true =>
      simp only [d77095, d76765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d77096 q = 1) : d76766 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d77096, d76766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77096, d76766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d77097 q = 1) : d76767 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d77097, d76767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77097, d76767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d77098 q = 1) : d76768 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d77098, d76768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77098, d76768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d77099 q = 1) : d76769 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d77099, d76769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77099, d76769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d77100 q = 1) : d76770 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d77100, d76770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77100, d76770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11111 (p : Pattern) (ha : d75630 p = 1) (hb : d77106 p = 1) : d76776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d77101 q = 1) : d76771 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d77101, d76771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11110 q ha hb
    | true =>
      simp only [d77101, d76771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d77102 q = 1) : d76772 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d77102, d76772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77102, d76772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d77103 q = 1) : d76773 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d77103, d76773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77103, d76773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d77104 q = 1) : d76774 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d77104, d76774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77104, d76774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d77105 q = 1) : d76775 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d77105, d76775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77105, d76775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d77106 q = 1) : d76776 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d77106, d76776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77106, d76776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11112 (p : Pattern) (ha : d75630 p = 1) (hb : d77112 p = 1) : d76782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d77107 q = 1) : d76777 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d77107, d76777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11111 q ha hb
    | true =>
      simp only [d77107, d76777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d77108 q = 1) : d76778 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d77108, d76778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77108, d76778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d77109 q = 1) : d76779 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d77109, d76779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77109, d76779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d77110 q = 1) : d76780 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d77110, d76780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77110, d76780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d77111 q = 1) : d76781 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d77111, d76781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77111, d76781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d77112 q = 1) : d76782 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d77112, d76782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77112, d76782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11113 (p : Pattern) (ha : d68228 p = 1) (hb : d76455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51894 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4737 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8901 q ha hb
    | true =>
      simp only [d4737, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5350 q = 1) (hb : d68224 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d68224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5350, d68224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
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
  have h5 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68225 q = 1) (hb : d76452 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68225, d76452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d68225, d76452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68226 q = 1) (hb : d76453 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68226, d76453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68226, d76453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68227 q = 1) (hb : d76454 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68227, d76454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68227, d76454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68228 q = 1) (hb : d76455 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68228, d76455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68228, d76455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11114 (p : Pattern) (ha : d68233 p = 1) (hb : d76459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51894 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4737 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8901 q ha hb
    | true =>
      simp only [d4737, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5350 q = 1) (hb : d68224 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d68224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5350, d68224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
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
  have h5 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68225 q = 1) (hb : d76452 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68225, d76452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d68225, d76452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68226 q = 1) (hb : d76453 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68226, d76453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68226, d76453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68227 q = 1) (hb : d76454 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68227, d76454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68227, d76454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51901 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5356 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8903 q ha hb
    | true =>
      simp only [d5356, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5357 q = 1) (hb : d68229 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d68229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5357, d68229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d68230 q = 1) (hb : d76456 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68230, d76456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d68230, d76456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d68231 q = 1) (hb : d76457 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68231, d76457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68231, d76457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d68232 q = 1) (hb : d76458 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68232, d76458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68232, d76458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d68233 q = 1) (hb : d76459 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68233, d76459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d68233, d76459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro11115 (p : Pattern) (ha : d68238 p = 1) (hb : d76464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51901 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5356 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8903 q ha hb
    | true =>
      simp only [d5356, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5357 q = 1) (hb : d68229 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d68229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5357, d68229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
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
  have h6 (q : Pattern) (ha : d68230 q = 1) (hb : d76456 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68230, d76456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d68230, d76456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68231 q = 1) (hb : d76457 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68231, d76457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68231, d76457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68232 q = 1) (hb : d76458 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68232, d76458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68232, d76458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68238 q = 1) (hb : d76464 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68238, d76464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68238, d76464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11116 (p : Pattern) (ha : d68248 p = 1) (hb : d76473 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5378 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8906 q ha hb
    | true =>
      simp only [d5378, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5379 q = 1) (hb : d68244 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d68244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5379, d68244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
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
  have h6 (q : Pattern) (ha : d68245 q = 1) (hb : d76470 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68245, d76470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d68245, d76470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68246 q = 1) (hb : d76471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68246, d76471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68246, d76471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68247 q = 1) (hb : d76472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68247, d76472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68247, d76472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68248 q = 1) (hb : d76473 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68248, d76473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68248, d76473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11117 (p : Pattern) (ha : d68254 p = 1) (hb : d76479 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68234 q = 1) (hb : d76460 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68234, d76460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11113 q ha hb
    | true =>
      simp only [d68234, d76460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11114 q ha hb
  have h2 (q : Pattern) (ha : d68235 q = 1) (hb : d76461 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68235, d76461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68235, d76461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68236 q = 1) (hb : d76462 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68236, d76462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68236, d76462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68237 q = 1) (hb : d76463 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68237, d76463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68237, d76463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68239 q = 1) (hb : d76465 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68239, d76465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68239, d76465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11115 q ha hb
  have h6 (q : Pattern) (ha : d68240 q = 1) (hb : d76466 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68240, d76466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68240, d76466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d68241 q = 1) (hb : d76467 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68241, d76467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68241, d76467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d68242 q = 1) (hb : d76468 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68242, d76468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68242, d76468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d68243 q = 1) (hb : d76469 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68243, d76469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68243, d76469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68249 q = 1) (hb : d76474 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68249, d76474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68249, d76474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11116 q ha hb
  have h11 (q : Pattern) (ha : d68250 q = 1) (hb : d76475 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68250, d76475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68250, d76475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d68251 q = 1) (hb : d76476 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68251, d76476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68251, d76476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d68252 q = 1) (hb : d76477 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68252, d76477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68252, d76477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d68253 q = 1) (hb : d76478 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68253, d76478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68253, d76478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d68254 q = 1) (hb : d76479 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68254, d76479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68254, d76479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11118 (p : Pattern) (ha : d68264 p = 1) (hb : d76490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52007 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52136 q = 1) (hb : d76485 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52136, d76485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9464 q hb ha
    | true =>
      simp only [d52136, d76485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68260 q = 1) (hb : d76486 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68260, d76486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68260, d76486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d4737 q = 1) (hb : d52138 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8901 q ha hb
    | true =>
      simp only [d4737, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5350 q = 1) (hb : d52139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d52139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5350, d52139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68261 q = 1) (hb : d76487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68261, d76487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68261, d76487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68262 q = 1) (hb : d76488 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68262, d76488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68262, d76488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68263 q = 1) (hb : d76489 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68263, d76489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68263, d76489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68264 q = 1) (hb : d76490 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68264, d76490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68264, d76490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11119 (p : Pattern) (ha : d68269 p = 1) (hb : d76496 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52007 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52136 q = 1) (hb : d76485 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52136, d76485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9464 q hb ha
    | true =>
      simp only [d52136, d76485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68260 q = 1) (hb : d76486 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68260, d76486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68260, d76486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d4737 q = 1) (hb : d52138 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8901 q ha hb
    | true =>
      simp only [d4737, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5350 q = 1) (hb : d52139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d52139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5350, d52139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68261 q = 1) (hb : d76487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68261, d76487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68261, d76487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68262 q = 1) (hb : d76488 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68262, d76488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68262, d76488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68263 q = 1) (hb : d76489 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68263, d76489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68263, d76489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52023 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52154 q = 1) (hb : d76491 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52154, d76491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9466 q hb ha
    | true =>
      simp only [d52154, d76491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d68265 q = 1) (hb : d76492 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68265, d76492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68265, d76492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d5356 q = 1) (hb : d52156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d52156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8903 q ha hb
    | true =>
      simp only [d5356, d52156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5357 q = 1) (hb : d52157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d52157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5357, d52157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d68266 q = 1) (hb : d76493 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68266, d76493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68266, d76493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d68267 q = 1) (hb : d76494 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68267, d76494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68267, d76494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d68268 q = 1) (hb : d76495 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68268, d76495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68268, d76495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d68269 q = 1) (hb : d76496 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68269, d76496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d68269, d76496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro11120 (p : Pattern) (ha : d68274 p = 1) (hb : d76501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52023 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52154 q = 1) (hb : d76491 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52154, d76491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9466 q hb ha
    | true =>
      simp only [d52154, d76491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68265 q = 1) (hb : d76492 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68265, d76492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68265, d76492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d5356 q = 1) (hb : d52156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d52156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8903 q ha hb
    | true =>
      simp only [d5356, d52156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5357 q = 1) (hb : d52157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d52157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5357, d52157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68266 q = 1) (hb : d76493 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68266, d76493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68266, d76493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68267 q = 1) (hb : d76494 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68267, d76494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68267, d76494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68268 q = 1) (hb : d76495 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68268, d76495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68268, d76495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68274 q = 1) (hb : d76501 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68274, d76501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68274, d76501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11121 (p : Pattern) (ha : d68284 p = 1) (hb : d76512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52061 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52196 q = 1) (hb : d76507 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52196, d76507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9469 q hb ha
    | true =>
      simp only [d52196, d76507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68280 q = 1) (hb : d76508 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68280, d76508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68280, d76508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d5378 q = 1) (hb : d52198 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d52198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8906 q ha hb
    | true =>
      simp only [d5378, d52198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5379 q = 1) (hb : d52199 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d52199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5379, d52199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68281 q = 1) (hb : d76509 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68281, d76509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68281, d76509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68282 q = 1) (hb : d76510 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68282, d76510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68282, d76510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68283 q = 1) (hb : d76511 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68283, d76511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68283, d76511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68284 q = 1) (hb : d76512 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68284, d76512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68284, d76512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11122 (p : Pattern) (ha : d68290 p = 1) (hb : d76518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68270 q = 1) (hb : d76497 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68270, d76497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11118 q ha hb
    | true =>
      simp only [d68270, d76497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11119 q ha hb
  have h2 (q : Pattern) (ha : d68271 q = 1) (hb : d76498 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68271, d76498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68271, d76498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68272 q = 1) (hb : d76499 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68272, d76499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68272, d76499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68273 q = 1) (hb : d76500 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68273, d76500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68273, d76500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68275 q = 1) (hb : d76502 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68275, d76502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68275, d76502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11120 q ha hb
  have h6 (q : Pattern) (ha : d68276 q = 1) (hb : d76503 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68276, d76503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68276, d76503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d68277 q = 1) (hb : d76504 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68277, d76504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68277, d76504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d68278 q = 1) (hb : d76505 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68278, d76505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68278, d76505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d68279 q = 1) (hb : d76506 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68279, d76506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68279, d76506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68285 q = 1) (hb : d76513 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68285, d76513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68285, d76513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11121 q ha hb
  have h11 (q : Pattern) (ha : d68286 q = 1) (hb : d76514 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68286, d76514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68286, d76514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d68287 q = 1) (hb : d76515 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68287, d76515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68287, d76515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d68288 q = 1) (hb : d76516 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68288, d76516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68288, d76516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d68289 q = 1) (hb : d76517 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68289, d76517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68289, d76517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d68290 q = 1) (hb : d76518 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68290, d76518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68290, d76518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11123 (p : Pattern) (ha : d68296 p = 1) (hb : d76524 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d68255 q = 1) (hb : d76480 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68255, d76480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68255, d76480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11117 q ha hb
  have h6 (q : Pattern) (ha : d68256 q = 1) (hb : d76481 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68256, d76481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68256, d76481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68257 q = 1) (hb : d76482 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68257, d76482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68257, d76482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68258 q = 1) (hb : d76483 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68258, d76483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68258, d76483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68259 q = 1) (hb : d76484 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68259, d76484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d68259, d76484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68291 q = 1) (hb : d76519 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68291, d76519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68291, d76519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11122 q ha hb
  have h11 (q : Pattern) (ha : d68292 q = 1) (hb : d76520 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68292, d76520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68292, d76520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d68293 q = 1) (hb : d76521 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68293, d76521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68293, d76521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d68294 q = 1) (hb : d76522 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68294, d76522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68294, d76522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d68295 q = 1) (hb : d76523 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68295, d76523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68295, d76523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d68296 q = 1) (hb : d76524 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68296, d76524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68296, d76524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11124 (p : Pattern) (ha : d68301 p = 1) (hb : d76530 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52234 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52308 q = 1) (hb : d76525 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52308, d76525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9476 q hb ha
    | true =>
      simp only [d52308, d76525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68297 q = 1) (hb : d76526 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68297, d76526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68297, d76526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d5400 q = 1) (hb : d52310 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d52310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8927 q ha hb
    | true =>
      simp only [d5400, d52310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5401 q = 1) (hb : d52311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5401, d52311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5401, d52311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68298 q = 1) (hb : d76527 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68298, d76527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68298, d76527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68299 q = 1) (hb : d76528 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68299, d76528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68299, d76528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68300 q = 1) (hb : d76529 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68300, d76529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68300, d76529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68301 q = 1) (hb : d76530 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68301, d76530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68301, d76530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11125 (p : Pattern) (ha : d68306 p = 1) (hb : d76536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52234 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52308 q = 1) (hb : d76525 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52308, d76525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9476 q hb ha
    | true =>
      simp only [d52308, d76525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68297 q = 1) (hb : d76526 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68297, d76526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68297, d76526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d5400 q = 1) (hb : d52310 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d52310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8927 q ha hb
    | true =>
      simp only [d5400, d52310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5401 q = 1) (hb : d52311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5401, d52311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5401, d52311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68298 q = 1) (hb : d76527 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68298, d76527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68298, d76527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68299 q = 1) (hb : d76528 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68299, d76528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68299, d76528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68300 q = 1) (hb : d76529 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68300, d76529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68300, d76529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52247 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52328 q = 1) (hb : d76531 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52328, d76531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9478 q hb ha
    | true =>
      simp only [d52328, d76531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d68302 q = 1) (hb : d76532 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68302, d76532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68302, d76532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d5407 q = 1) (hb : d52330 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d52330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8929 q ha hb
    | true =>
      simp only [d5407, d52330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5408 q = 1) (hb : d52331 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5408, d52331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5408, d52331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d68303 q = 1) (hb : d76533 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68303, d76533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68303, d76533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d68304 q = 1) (hb : d76534 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68304, d76534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68304, d76534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d68305 q = 1) (hb : d76535 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68305, d76535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68305, d76535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d68306 q = 1) (hb : d76536 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68306, d76536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d68306, d76536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro11126 (p : Pattern) (ha : d68311 p = 1) (hb : d76541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52247 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52328 q = 1) (hb : d76531 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52328, d76531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9478 q hb ha
    | true =>
      simp only [d52328, d76531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68302 q = 1) (hb : d76532 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68302, d76532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68302, d76532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d5407 q = 1) (hb : d52330 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d52330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8929 q ha hb
    | true =>
      simp only [d5407, d52330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5408 q = 1) (hb : d52331 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5408, d52331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5408, d52331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68303 q = 1) (hb : d76533 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68303, d76533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68303, d76533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68304 q = 1) (hb : d76534 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68304, d76534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68304, d76534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68305 q = 1) (hb : d76535 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68305, d76535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68305, d76535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68311 q = 1) (hb : d76541 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68311, d76541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68311, d76541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11127 (p : Pattern) (ha : d68321 p = 1) (hb : d76552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52393 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52394 q = 1) (hb : d76547 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52394, d76547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9481 q hb ha
    | true =>
      simp only [d52394, d76547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68317 q = 1) (hb : d76548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68317, d76548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68317, d76548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d5429 q = 1) (hb : d52401 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5429, d52401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9040 q ha hb
    | true =>
      simp only [d5429, d52401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5430 q = 1) (hb : d52402 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5430, d52402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5430, d52402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68318 q = 1) (hb : d76549 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68318, d76549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68318, d76549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68319 q = 1) (hb : d76550 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68319, d76550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68319, d76550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68320 q = 1) (hb : d76551 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68320, d76551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68320, d76551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68321 q = 1) (hb : d76552 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68321, d76552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68321, d76552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11128 (p : Pattern) (ha : d68327 p = 1) (hb : d76558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68307 q = 1) (hb : d76537 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68307, d76537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11124 q ha hb
    | true =>
      simp only [d68307, d76537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11125 q ha hb
  have h2 (q : Pattern) (ha : d68308 q = 1) (hb : d76538 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68308, d76538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68308, d76538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68309 q = 1) (hb : d76539 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68309, d76539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68309, d76539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68310 q = 1) (hb : d76540 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68310, d76540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68310, d76540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68312 q = 1) (hb : d76542 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68312, d76542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68312, d76542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11126 q ha hb
  have h6 (q : Pattern) (ha : d68313 q = 1) (hb : d76543 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68313, d76543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68313, d76543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d68314 q = 1) (hb : d76544 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68314, d76544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68314, d76544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d68315 q = 1) (hb : d76545 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68315, d76545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68315, d76545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d68316 q = 1) (hb : d76546 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68316, d76546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68316, d76546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68322 q = 1) (hb : d76553 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68322, d76553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68322, d76553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11127 q ha hb
  have h11 (q : Pattern) (ha : d68323 q = 1) (hb : d76554 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68323, d76554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68323, d76554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d68324 q = 1) (hb : d76555 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68324, d76555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68324, d76555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d68325 q = 1) (hb : d76556 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68325, d76556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68325, d76556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d68326 q = 1) (hb : d76557 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68326, d76557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68326, d76557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d68327 q = 1) (hb : d76558 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68327, d76558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68327, d76558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11129 (p : Pattern) (ha : d68333 p = 1) (hb : d76564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68328 q = 1) (hb : d76559 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68328, d76559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68328, d76559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11128 q ha hb
  have h2 (q : Pattern) (ha : d68329 q = 1) (hb : d76560 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68329, d76560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68329, d76560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68330 q = 1) (hb : d76561 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68330, d76561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68330, d76561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68331 q = 1) (hb : d76562 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68331, d76562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68331, d76562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68332 q = 1) (hb : d76563 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68332, d76563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68332, d76563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d68333 q = 1) (hb : d76564 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68333, d76564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68333, d76564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11130 (p : Pattern) (ha : d68339 p = 1) (hb : d76571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52456 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52529 q = 1) (hb : d76566 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52529, d76566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9488 q hb ha
    | true =>
      simp only [d52529, d76566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68335 q = 1) (hb : d76567 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68335, d76567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68335, d76567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d6160 q = 1) (hb : d52531 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, d52531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8946 q ha hb
    | true =>
      simp only [d6160, d52531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6161 q = 1) (hb : d52532 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6161, d52532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6161, d52532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68336 q = 1) (hb : d76568 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68336, d76568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68336, d76568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68337 q = 1) (hb : d76569 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68337, d76569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68337, d76569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68338 q = 1) (hb : d76570 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68338, d76570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68338, d76570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68339 q = 1) (hb : d76571 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68339, d76571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68339, d76571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11131 (p : Pattern) (ha : d68344 p = 1) (hb : d76577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52456 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52529 q = 1) (hb : d76566 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52529, d76566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9488 q hb ha
    | true =>
      simp only [d52529, d76566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68335 q = 1) (hb : d76567 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68335, d76567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68335, d76567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d6160 q = 1) (hb : d52531 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, d52531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8946 q ha hb
    | true =>
      simp only [d6160, d52531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6161 q = 1) (hb : d52532 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6161, d52532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6161, d52532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68336 q = 1) (hb : d76568 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68336, d76568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68336, d76568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68337 q = 1) (hb : d76569 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68337, d76569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68337, d76569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68338 q = 1) (hb : d76570 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68338, d76570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68338, d76570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52469 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52549 q = 1) (hb : d76572 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52549, d76572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9490 q hb ha
    | true =>
      simp only [d52549, d76572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d68340 q = 1) (hb : d76573 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68340, d76573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68340, d76573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d6181 q = 1) (hb : d52551 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, d52551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8948 q ha hb
    | true =>
      simp only [d6181, d52551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6182 q = 1) (hb : d52552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6182, d52552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6182, d52552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d68341 q = 1) (hb : d76574 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68341, d76574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68341, d76574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d68342 q = 1) (hb : d76575 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68342, d76575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68342, d76575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d68343 q = 1) (hb : d76576 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68343, d76576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68343, d76576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d68344 q = 1) (hb : d76577 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68344, d76577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d68344, d76577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro11132 (p : Pattern) (ha : d68349 p = 1) (hb : d76582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52469 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52549 q = 1) (hb : d76572 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52549, d76572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9490 q hb ha
    | true =>
      simp only [d52549, d76572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68340 q = 1) (hb : d76573 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68340, d76573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68340, d76573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d6181 q = 1) (hb : d52551 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, d52551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8948 q ha hb
    | true =>
      simp only [d6181, d52551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6182 q = 1) (hb : d52552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6182, d52552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6182, d52552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68341 q = 1) (hb : d76574 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68341, d76574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68341, d76574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68342 q = 1) (hb : d76575 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68342, d76575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68342, d76575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68343 q = 1) (hb : d76576 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68343, d76576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68343, d76576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68349 q = 1) (hb : d76582 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68349, d76582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68349, d76582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11133 (p : Pattern) (ha : d68359 p = 1) (hb : d76593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52630 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52631 q = 1) (hb : d76588 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52631, d76588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9493 q hb ha
    | true =>
      simp only [d52631, d76588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68355 q = 1) (hb : d76589 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68355, d76589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68355, d76589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d6234 q = 1) (hb : d52638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6234, d52638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9047 q ha hb
    | true =>
      simp only [d6234, d52638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6235 q = 1) (hb : d52639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6235, d52639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6235, d52639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68356 q = 1) (hb : d76590 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68356, d76590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68356, d76590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68357 q = 1) (hb : d76591 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68357, d76591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68357, d76591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68358 q = 1) (hb : d76592 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68358, d76592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68358, d76592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68359 q = 1) (hb : d76593 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68359, d76593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68359, d76593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11134 (p : Pattern) (ha : d68365 p = 1) (hb : d76599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68345 q = 1) (hb : d76578 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68345, d76578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11130 q ha hb
    | true =>
      simp only [d68345, d76578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11131 q ha hb
  have h2 (q : Pattern) (ha : d68346 q = 1) (hb : d76579 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68346, d76579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68346, d76579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68347 q = 1) (hb : d76580 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68347, d76580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68347, d76580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68348 q = 1) (hb : d76581 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68348, d76581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68348, d76581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68350 q = 1) (hb : d76583 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68350, d76583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68350, d76583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11132 q ha hb
  have h6 (q : Pattern) (ha : d68351 q = 1) (hb : d76584 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68351, d76584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68351, d76584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d68352 q = 1) (hb : d76585 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68352, d76585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68352, d76585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d68353 q = 1) (hb : d76586 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68353, d76586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68353, d76586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d68354 q = 1) (hb : d76587 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68354, d76587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68354, d76587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68360 q = 1) (hb : d76594 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68360, d76594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68360, d76594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11133 q ha hb
  have h11 (q : Pattern) (ha : d68361 q = 1) (hb : d76595 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68361, d76595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68361, d76595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d68362 q = 1) (hb : d76596 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68362, d76596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68362, d76596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d68363 q = 1) (hb : d76597 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68363, d76597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68363, d76597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d68364 q = 1) (hb : d76598 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68364, d76598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68364, d76598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d68365 q = 1) (hb : d76599 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68365, d76599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68365, d76599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11135 (p : Pattern) (ha : d68371 p = 1) (hb : d76605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68366 q = 1) (hb : d76600 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68366, d76600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68366, d76600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11134 q ha hb
  have h2 (q : Pattern) (ha : d68367 q = 1) (hb : d76601 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68367, d76601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68367, d76601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68368 q = 1) (hb : d76602 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68368, d76602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68368, d76602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68369 q = 1) (hb : d76603 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68369, d76603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68369, d76603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68370 q = 1) (hb : d76604 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68370, d76604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68370, d76604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d68371 q = 1) (hb : d76605 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68371, d76605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68371, d76605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11136 (p : Pattern) (ha : d68378 p = 1) (hb : d76613 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52739 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52809 q = 1) (hb : d76608 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52809, d76608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9500 q hb ha
    | true =>
      simp only [d52809, d76608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68374 q = 1) (hb : d76609 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68374, d76609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68374, d76609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d6299 q = 1) (hb : d52811 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, d52811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8965 q ha hb
    | true =>
      simp only [d6299, d52811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6300 q = 1) (hb : d52812 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6300, d52812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6300, d52812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68375 q = 1) (hb : d76610 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68375, d76610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68375, d76610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68376 q = 1) (hb : d76611 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68376, d76611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68376, d76611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68377 q = 1) (hb : d76612 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68377, d76612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68377, d76612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68378 q = 1) (hb : d76613 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68378, d76613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68378, d76613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11137 (p : Pattern) (ha : d68383 p = 1) (hb : d76619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52739 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52809 q = 1) (hb : d76608 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52809, d76608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9500 q hb ha
    | true =>
      simp only [d52809, d76608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68374 q = 1) (hb : d76609 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68374, d76609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68374, d76609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d6299 q = 1) (hb : d52811 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, d52811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8965 q ha hb
    | true =>
      simp only [d6299, d52811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6300 q = 1) (hb : d52812 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6300, d52812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6300, d52812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68375 q = 1) (hb : d76610 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68375, d76610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68375, d76610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68376 q = 1) (hb : d76611 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68376, d76611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68376, d76611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68377 q = 1) (hb : d76612 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68377, d76612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68377, d76612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52752 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52829 q = 1) (hb : d76614 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52829, d76614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9502 q hb ha
    | true =>
      simp only [d52829, d76614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d68379 q = 1) (hb : d76615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68379, d76615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68379, d76615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d6320 q = 1) (hb : d52831 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, d52831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8967 q ha hb
    | true =>
      simp only [d6320, d52831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6321 q = 1) (hb : d52832 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6321, d52832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6321, d52832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d68380 q = 1) (hb : d76616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68380, d76616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68380, d76616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d68381 q = 1) (hb : d76617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68381, d76617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68381, d76617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d68382 q = 1) (hb : d76618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68382, d76618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68382, d76618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d68383 q = 1) (hb : d76619 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68383, d76619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d68383, d76619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro11138 (p : Pattern) (ha : d68388 p = 1) (hb : d76624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52752 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52829 q = 1) (hb : d76614 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52829, d76614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9502 q hb ha
    | true =>
      simp only [d52829, d76614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68379 q = 1) (hb : d76615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68379, d76615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68379, d76615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d6320 q = 1) (hb : d52831 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, d52831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8967 q ha hb
    | true =>
      simp only [d6320, d52831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6321 q = 1) (hb : d52832 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6321, d52832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6321, d52832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68380 q = 1) (hb : d76616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68380, d76616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68380, d76616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68381 q = 1) (hb : d76617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68381, d76617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68381, d76617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68382 q = 1) (hb : d76618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68382, d76618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68382, d76618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68388 q = 1) (hb : d76624 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68388, d76624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68388, d76624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11139 (p : Pattern) (ha : d68398 p = 1) (hb : d76635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52924 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52925 q = 1) (hb : d76630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52925, d76630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9505 q hb ha
    | true =>
      simp only [d52925, d76630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68394 q = 1) (hb : d76631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68394, d76631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68394, d76631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d6379 q = 1) (hb : d52932 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6379, d52932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9054 q ha hb
    | true =>
      simp only [d6379, d52932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6380 q = 1) (hb : d52933 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6380, d52933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6380, d52933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68395 q = 1) (hb : d76632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68395, d76632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68395, d76632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68396 q = 1) (hb : d76633 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68396, d76633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68396, d76633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68397 q = 1) (hb : d76634 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68397, d76634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68397, d76634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68398 q = 1) (hb : d76635 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68398, d76635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68398, d76635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11140 (p : Pattern) (ha : d68404 p = 1) (hb : d76641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68384 q = 1) (hb : d76620 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68384, d76620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11136 q ha hb
    | true =>
      simp only [d68384, d76620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11137 q ha hb
  have h2 (q : Pattern) (ha : d68385 q = 1) (hb : d76621 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68385, d76621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68385, d76621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68386 q = 1) (hb : d76622 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68386, d76622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68386, d76622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68387 q = 1) (hb : d76623 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68387, d76623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68387, d76623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68389 q = 1) (hb : d76625 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68389, d76625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68389, d76625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11138 q ha hb
  have h6 (q : Pattern) (ha : d68390 q = 1) (hb : d76626 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68390, d76626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68390, d76626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d68391 q = 1) (hb : d76627 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68391, d76627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68391, d76627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d68392 q = 1) (hb : d76628 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68392, d76628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68392, d76628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d68393 q = 1) (hb : d76629 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68393, d76629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68393, d76629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68399 q = 1) (hb : d76636 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68399, d76636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68399, d76636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11139 q ha hb
  have h11 (q : Pattern) (ha : d68400 q = 1) (hb : d76637 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68400, d76637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68400, d76637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d68401 q = 1) (hb : d76638 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68401, d76638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68401, d76638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d68402 q = 1) (hb : d76639 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68402, d76639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68402, d76639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d68403 q = 1) (hb : d76640 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68403, d76640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68403, d76640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d68404 q = 1) (hb : d76641 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68404, d76641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68404, d76641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11141 (p : Pattern) (ha : d68410 p = 1) (hb : d76647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68405 q = 1) (hb : d76642 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68405, d76642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68405, d76642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11140 q ha hb
  have h2 (q : Pattern) (ha : d68406 q = 1) (hb : d76643 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68406, d76643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68406, d76643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68407 q = 1) (hb : d76644 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68407, d76644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68407, d76644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68408 q = 1) (hb : d76645 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68408, d76645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68408, d76645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68409 q = 1) (hb : d76646 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68409, d76646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68409, d76646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d68410 q = 1) (hb : d76647 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68410, d76647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68410, d76647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11142 (p : Pattern) (ha : d68418 p = 1) (hb : d76656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53060 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53124 q = 1) (hb : d76651 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53124, d76651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9512 q hb ha
    | true =>
      simp only [d53124, d76651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68414 q = 1) (hb : d76652 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68414, d76652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68414, d76652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d6445 q = 1) (hb : d53126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, d53126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8984 q ha hb
    | true =>
      simp only [d6445, d53126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6446 q = 1) (hb : d53127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6446, d53127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6446, d53127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68415 q = 1) (hb : d76653 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68415, d76653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68415, d76653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68416 q = 1) (hb : d76654 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68416, d76654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68416, d76654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68417 q = 1) (hb : d76655 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68417, d76655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68417, d76655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68418 q = 1) (hb : d76656 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68418, d76656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68418, d76656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11143 (p : Pattern) (ha : d68423 p = 1) (hb : d76662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53060 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53124 q = 1) (hb : d76651 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53124, d76651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9512 q hb ha
    | true =>
      simp only [d53124, d76651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68414 q = 1) (hb : d76652 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68414, d76652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68414, d76652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d6445 q = 1) (hb : d53126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, d53126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8984 q ha hb
    | true =>
      simp only [d6445, d53126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6446 q = 1) (hb : d53127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6446, d53127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6446, d53127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68415 q = 1) (hb : d76653 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68415, d76653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68415, d76653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68416 q = 1) (hb : d76654 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68416, d76654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68416, d76654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68417 q = 1) (hb : d76655 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68417, d76655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68417, d76655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53073 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53144 q = 1) (hb : d76657 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53144, d76657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9514 q hb ha
    | true =>
      simp only [d53144, d76657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d68419 q = 1) (hb : d76658 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68419, d76658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68419, d76658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d6466 q = 1) (hb : d53146 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, d53146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8986 q ha hb
    | true =>
      simp only [d6466, d53146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6467 q = 1) (hb : d53147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6467, d53147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6467, d53147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d68420 q = 1) (hb : d76659 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68420, d76659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68420, d76659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d68421 q = 1) (hb : d76660 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68421, d76660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68421, d76660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d68422 q = 1) (hb : d76661 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68422, d76661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68422, d76661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d68423 q = 1) (hb : d76662 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68423, d76662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d68423, d76662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro11144 (p : Pattern) (ha : d68428 p = 1) (hb : d76667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53073 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53144 q = 1) (hb : d76657 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53144, d76657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9514 q hb ha
    | true =>
      simp only [d53144, d76657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68419 q = 1) (hb : d76658 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68419, d76658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68419, d76658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d6466 q = 1) (hb : d53146 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, d53146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8986 q ha hb
    | true =>
      simp only [d6466, d53146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6467 q = 1) (hb : d53147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6467, d53147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6467, d53147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68420 q = 1) (hb : d76659 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68420, d76659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68420, d76659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68421 q = 1) (hb : d76660 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68421, d76660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68421, d76660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68422 q = 1) (hb : d76661 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68422, d76661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68422, d76661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68428 q = 1) (hb : d76667 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68428, d76667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68428, d76667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11145 (p : Pattern) (ha : d68438 p = 1) (hb : d76678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53239 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53240 q = 1) (hb : d76673 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53240, d76673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9517 q hb ha
    | true =>
      simp only [d53240, d76673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68434 q = 1) (hb : d76674 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68434, d76674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68434, d76674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d6525 q = 1) (hb : d53247 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6525, d53247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9061 q ha hb
    | true =>
      simp only [d6525, d53247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6526 q = 1) (hb : d53248 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6526, d53248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6526, d53248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68435 q = 1) (hb : d76675 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68435, d76675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68435, d76675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68436 q = 1) (hb : d76676 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68436, d76676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68436, d76676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68437 q = 1) (hb : d76677 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68437, d76677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68437, d76677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68438 q = 1) (hb : d76678 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68438, d76678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68438, d76678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11146 (p : Pattern) (ha : d68444 p = 1) (hb : d76684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68424 q = 1) (hb : d76663 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68424, d76663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11142 q ha hb
    | true =>
      simp only [d68424, d76663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11143 q ha hb
  have h2 (q : Pattern) (ha : d68425 q = 1) (hb : d76664 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68425, d76664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68425, d76664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68426 q = 1) (hb : d76665 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68426, d76665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68426, d76665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68427 q = 1) (hb : d76666 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68427, d76666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68427, d76666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68429 q = 1) (hb : d76668 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68429, d76668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68429, d76668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11144 q ha hb
  have h6 (q : Pattern) (ha : d68430 q = 1) (hb : d76669 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68430, d76669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68430, d76669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d68431 q = 1) (hb : d76670 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68431, d76670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68431, d76670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d68432 q = 1) (hb : d76671 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68432, d76671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68432, d76671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d68433 q = 1) (hb : d76672 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68433, d76672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68433, d76672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68439 q = 1) (hb : d76679 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68439, d76679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68439, d76679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11145 q ha hb
  have h11 (q : Pattern) (ha : d68440 q = 1) (hb : d76680 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68440, d76680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68440, d76680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d68441 q = 1) (hb : d76681 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68441, d76681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68441, d76681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d68442 q = 1) (hb : d76682 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68442, d76682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68442, d76682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d68443 q = 1) (hb : d76683 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68443, d76683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68443, d76683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d68444 q = 1) (hb : d76684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68444, d76684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68444, d76684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11147 (p : Pattern) (ha : d68450 p = 1) (hb : d76690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68445 q = 1) (hb : d76685 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68445, d76685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68445, d76685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11146 q ha hb
  have h2 (q : Pattern) (ha : d68446 q = 1) (hb : d76686 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68446, d76686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68446, d76686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68447 q = 1) (hb : d76687 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68447, d76687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68447, d76687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68448 q = 1) (hb : d76688 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68448, d76688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68448, d76688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68449 q = 1) (hb : d76689 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68449, d76689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68449, d76689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d68450 q = 1) (hb : d76690 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68450, d76690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68450, d76690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11148 (p : Pattern) (ha : d68459 p = 1) (hb : d76700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53381 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53441 q = 1) (hb : d76695 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53441, d76695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9524 q hb ha
    | true =>
      simp only [d53441, d76695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68455 q = 1) (hb : d76696 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68455, d76696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68455, d76696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d6592 q = 1) (hb : d53443 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9003 q ha hb
    | true =>
      simp only [d6592, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6593 q = 1) (hb : d53444 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6593, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6593, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68456 q = 1) (hb : d76697 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68456, d76697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68456, d76697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68457 q = 1) (hb : d76698 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68457, d76698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68457, d76698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68458 q = 1) (hb : d76699 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68458, d76699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68458, d76699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68459 q = 1) (hb : d76700 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68459, d76700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68459, d76700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11149 (p : Pattern) (ha : d68464 p = 1) (hb : d76706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53381 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53441 q = 1) (hb : d76695 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53441, d76695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9524 q hb ha
    | true =>
      simp only [d53441, d76695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68455 q = 1) (hb : d76696 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68455, d76696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68455, d76696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d6592 q = 1) (hb : d53443 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9003 q ha hb
    | true =>
      simp only [d6592, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6593 q = 1) (hb : d53444 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6593, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6593, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68456 q = 1) (hb : d76697 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68456, d76697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68456, d76697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68457 q = 1) (hb : d76698 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68457, d76698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68457, d76698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68458 q = 1) (hb : d76699 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68458, d76699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68458, d76699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53394 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53461 q = 1) (hb : d76701 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53461, d76701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9526 q hb ha
    | true =>
      simp only [d53461, d76701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d68460 q = 1) (hb : d76702 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68460, d76702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68460, d76702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d6613 q = 1) (hb : d53463 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d53463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9005 q ha hb
    | true =>
      simp only [d6613, d53463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6614 q = 1) (hb : d53464 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6614, d53464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6614, d53464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d68461 q = 1) (hb : d76703 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68461, d76703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68461, d76703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d68462 q = 1) (hb : d76704 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68462, d76704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68462, d76704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d68463 q = 1) (hb : d76705 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68463, d76705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68463, d76705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d68464 q = 1) (hb : d76706 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68464, d76706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d68464, d76706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro11150 (p : Pattern) (ha : d68469 p = 1) (hb : d76711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53461 q = 1) (hb : d76701 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53461, d76701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9526 q hb ha
    | true =>
      simp only [d53461, d76701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68460 q = 1) (hb : d76702 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68460, d76702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68460, d76702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d6613 q = 1) (hb : d53463 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d53463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9005 q ha hb
    | true =>
      simp only [d6613, d53463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6614 q = 1) (hb : d53464 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6614, d53464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6614, d53464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68461 q = 1) (hb : d76703 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68461, d76703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68461, d76703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68462 q = 1) (hb : d76704 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68462, d76704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68462, d76704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68463 q = 1) (hb : d76705 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68463, d76705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68463, d76705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68469 q = 1) (hb : d76711 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68469, d76711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68469, d76711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11151 (p : Pattern) (ha : d68479 p = 1) (hb : d76722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53557 q = 1) (hb : d76717 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53557, d76717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9529 q hb ha
    | true =>
      simp only [d53557, d76717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68475 q = 1) (hb : d76718 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68475, d76718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68475, d76718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d6672 q = 1) (hb : d53564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6672, d53564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9068 q ha hb
    | true =>
      simp only [d6672, d53564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6673 q = 1) (hb : d53565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6673, d53565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6673, d53565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68476 q = 1) (hb : d76719 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68476, d76719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68476, d76719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68477 q = 1) (hb : d76720 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68477, d76720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68477, d76720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68478 q = 1) (hb : d76721 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68478, d76721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68478, d76721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68479 q = 1) (hb : d76722 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68479, d76722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68479, d76722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro11152 (p : Pattern) (ha : d68485 p = 1) (hb : d76728 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68465 q = 1) (hb : d76707 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68465, d76707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11148 q ha hb
    | true =>
      simp only [d68465, d76707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11149 q ha hb
  have h2 (q : Pattern) (ha : d68466 q = 1) (hb : d76708 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68466, d76708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68466, d76708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68467 q = 1) (hb : d76709 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68467, d76709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68467, d76709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68468 q = 1) (hb : d76710 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68468, d76710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68468, d76710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68470 q = 1) (hb : d76712 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68470, d76712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68470, d76712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11150 q ha hb
  have h6 (q : Pattern) (ha : d68471 q = 1) (hb : d76713 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68471, d76713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68471, d76713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d68472 q = 1) (hb : d76714 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68472, d76714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68472, d76714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d68473 q = 1) (hb : d76715 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68473, d76715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68473, d76715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d68474 q = 1) (hb : d76716 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68474, d76716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68474, d76716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68480 q = 1) (hb : d76723 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68480, d76723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68480, d76723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11151 q ha hb
  have h11 (q : Pattern) (ha : d68481 q = 1) (hb : d76724 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68481, d76724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68481, d76724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d68482 q = 1) (hb : d76725 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68482, d76725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68482, d76725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d68483 q = 1) (hb : d76726 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68483, d76726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68483, d76726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d68484 q = 1) (hb : d76727 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68484, d76727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68484, d76727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d68485 q = 1) (hb : d76728 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68485, d76728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68485, d76728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11153 (p : Pattern) (ha : d68491 p = 1) (hb : d76734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68486 q = 1) (hb : d76729 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68486, d76729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68486, d76729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11152 q ha hb
  have h2 (q : Pattern) (ha : d68487 q = 1) (hb : d76730 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68487, d76730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68487, d76730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68488 q = 1) (hb : d76731 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68488, d76731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68488, d76731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68489 q = 1) (hb : d76732 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68489, d76732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68489, d76732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68490 q = 1) (hb : d76733 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68490, d76733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68490, d76733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d68491 q = 1) (hb : d76734 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68491, d76734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68491, d76734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11154 (p : Pattern) (ha : d68497 p = 1) (hb : d76740 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d68334 q = 1) (hb : d76565 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d68334, d76565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11123 q ha hb
    | true =>
      simp only [d68334, d76565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11129 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d68372 q = 1) (hb : d76606 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d68372, d76606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68372, d76606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11135 q ha hb
  have h3 (q : Pattern) (ha : d68373 q = 1) (hb : d76607 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d68373, d76607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d68373, d76607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68411 q = 1) (hb : d76648 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d68411, d76648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68411, d76648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11141 q ha hb
  have h5 (q : Pattern) (ha : d68412 q = 1) (hb : d76649 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d68412, d76649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68412, d76649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d68413 q = 1) (hb : d76650 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d68413, d76650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68413, d76650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68451 q = 1) (hb : d76691 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d68451, d76691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68451, d76691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11147 q ha hb
  have h8 (q : Pattern) (ha : d68452 q = 1) (hb : d76692 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d68452, d76692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68452, d76692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68453 q = 1) (hb : d76693 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d68453, d76693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68453, d76693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68454 q = 1) (hb : d76694 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d68454, d76694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68454, d76694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d68492 q = 1) (hb : d76735 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d68492, d76735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68492, d76735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11153 q ha hb
  have h12 (q : Pattern) (ha : d68493 q = 1) (hb : d76736 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d68493, d76736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68493, d76736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d68494 q = 1) (hb : d76737 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d68494, d76737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68494, d76737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d68495 q = 1) (hb : d76738 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d68495, d76738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68495, d76738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d68496 q = 1) (hb : d76739 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d68496, d76739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68496, d76739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d68497 q = 1) (hb : d76740 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d68497, d76740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d68497, d76740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro11155 (p : Pattern) (ha : d68503 p = 1) (hb : d76746 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68498 q = 1) (hb : d76741 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d68498, d76741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11154 q ha hb
    | true =>
      simp only [d68498, d76741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d68499 q = 1) (hb : d76742 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d68499, d76742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68499, d76742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68500 q = 1) (hb : d76743 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d68500, d76743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68500, d76743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68501 q = 1) (hb : d76744 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d68501, d76744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68501, d76744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68502 q = 1) (hb : d76745 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d68502, d76745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68502, d76745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68503 q = 1) (hb : d76746 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d68503, d76746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68503, d76746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11156 (p : Pattern) (ha : d68509 p = 1) (hb : d76752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68504 q = 1) (hb : d76747 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d68504, d76747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11155 q ha hb
    | true =>
      simp only [d68504, d76747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d68505 q = 1) (hb : d76748 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d68505, d76748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68505, d76748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68506 q = 1) (hb : d76749 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d68506, d76749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68506, d76749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68507 q = 1) (hb : d76750 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d68507, d76750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68507, d76750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68508 q = 1) (hb : d76751 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d68508, d76751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68508, d76751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68509 q = 1) (hb : d76752 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d68509, d76752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68509, d76752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11157 (p : Pattern) (ha : d68515 p = 1) (hb : d76758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68510 q = 1) (hb : d76753 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d68510, d76753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11156 q ha hb
    | true =>
      simp only [d68510, d76753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d68511 q = 1) (hb : d76754 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d68511, d76754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68511, d76754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68512 q = 1) (hb : d76755 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d68512, d76755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68512, d76755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68513 q = 1) (hb : d76756 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d68513, d76756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68513, d76756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68514 q = 1) (hb : d76757 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d68514, d76757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68514, d76757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68515 q = 1) (hb : d76758 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d68515, d76758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68515, d76758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11158 (p : Pattern) (ha : d68521 p = 1) (hb : d76764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68516 q = 1) (hb : d76759 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d68516, d76759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11157 q ha hb
    | true =>
      simp only [d68516, d76759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d68517 q = 1) (hb : d76760 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d68517, d76760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68517, d76760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68518 q = 1) (hb : d76761 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d68518, d76761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68518, d76761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68519 q = 1) (hb : d76762 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d68519, d76762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68519, d76762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68520 q = 1) (hb : d76763 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d68520, d76763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68520, d76763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68521 q = 1) (hb : d76764 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d68521, d76764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68521, d76764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11159 (p : Pattern) (ha : d68527 p = 1) (hb : d76770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68522 q = 1) (hb : d76765 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d68522, d76765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11158 q ha hb
    | true =>
      simp only [d68522, d76765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d68523 q = 1) (hb : d76766 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d68523, d76766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68523, d76766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68524 q = 1) (hb : d76767 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d68524, d76767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68524, d76767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68525 q = 1) (hb : d76768 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d68525, d76768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68525, d76768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68526 q = 1) (hb : d76769 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d68526, d76769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68526, d76769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68527 q = 1) (hb : d76770 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d68527, d76770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68527, d76770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11160 (p : Pattern) (ha : d68533 p = 1) (hb : d76776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68528 q = 1) (hb : d76771 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d68528, d76771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11159 q ha hb
    | true =>
      simp only [d68528, d76771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d68529 q = 1) (hb : d76772 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d68529, d76772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68529, d76772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68530 q = 1) (hb : d76773 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d68530, d76773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68530, d76773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68531 q = 1) (hb : d76774 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d68531, d76774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68531, d76774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68532 q = 1) (hb : d76775 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d68532, d76775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68532, d76775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68533 q = 1) (hb : d76776 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d68533, d76776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68533, d76776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11161 (p : Pattern) (ha : d68539 p = 1) (hb : d76782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68534 q = 1) (hb : d76777 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d68534, d76777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11160 q ha hb
    | true =>
      simp only [d68534, d76777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d68535 q = 1) (hb : d76778 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d68535, d76778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68535, d76778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68536 q = 1) (hb : d76779 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d68536, d76779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68536, d76779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68537 q = 1) (hb : d76780 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d68537, d76780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68537, d76780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68538 q = 1) (hb : d76781 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d68538, d76781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68538, d76781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68539 q = 1) (hb : d76782 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d68539, d76782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68539, d76782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11162 (p : Pattern) (ha : d53647 p = 1) (hb : d75630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11026 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11027 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11034 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11035 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
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
theorem andIntro11163 (p : Pattern) (ha : d75630 p = 1) (hb : d82697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5856 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5898 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5898, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5898, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5899 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5900 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5901 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d82697 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro11164 (p : Pattern) (ha : d75630 p = 1) (hb : d82707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5874 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d82703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75630, d82703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d82707 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11165 (p : Pattern) (ha : d75630 p = 1) (hb : d82713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5903 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11036 q ha hb
    | true =>
      simp only [d5903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11037 q ha hb
  have h2 (q : Pattern) (ha : d5904 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82695 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d82695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82696 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82698 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11163 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82699 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d82700 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d82701 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d82702 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d82708 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11164 q ha hb
  have h11 (q : Pattern) (ha : d75630 q = 1) (hb : d82709 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d75630 q = 1) (hb : d82710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d82711 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d75630 q = 1) (hb : d82712 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d82713 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11166 (p : Pattern) (ha : d75630 p = 1) (hb : d82719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11162 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82714 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11165 q ha hb
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d82715 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d82716 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d82717 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d82718 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75630 q = 1) (hb : d82719 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d82719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro11167 (p : Pattern) (ha : d75630 p = 1) (hb : d82722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6000 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6001 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6001, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6001, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6002 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6003 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6004 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d82722 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro11168 (p : Pattern) (ha : d75630 p = 1) (hb : d82733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d82728 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82729 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d82729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75630, d82729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82730 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82731 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82732 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d82733 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11169 (p : Pattern) (ha : d75630 p = 1) (hb : d82739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6006 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11048 q ha hb
    | true =>
      simp only [d6006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11049 q ha hb
  have h2 (q : Pattern) (ha : d6007 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82720 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d82720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82721 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82723 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11167 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82724 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d82725 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d82726 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d82727 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d82734 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11168 q ha hb
  have h11 (q : Pattern) (ha : d75630 q = 1) (hb : d82735 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d75630 q = 1) (hb : d82736 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d82737 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d75630 q = 1) (hb : d82738 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d82739 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11170 (p : Pattern) (ha : d75630 p = 1) (hb : d82745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d82740 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11169 q ha hb
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d82741 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82742 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82743 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82744 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82745 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11171 (p : Pattern) (ha : d75630 p = 1) (hb : d82749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6128 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6129 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6129, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6129, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6130 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6131 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6132 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d82749 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro11172 (p : Pattern) (ha : d75630 p = 1) (hb : d82760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d82755 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d82756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75630, d82756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d82760 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11173 (p : Pattern) (ha : d75630 p = 1) (hb : d82766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6134 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11060 q ha hb
    | true =>
      simp only [d6134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11061 q ha hb
  have h2 (q : Pattern) (ha : d6135 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82747 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d82747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82748 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82750 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11171 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82751 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d82752 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d82753 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d82754 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d82761 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11172 q ha hb
  have h11 (q : Pattern) (ha : d75630 q = 1) (hb : d82762 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d75630 q = 1) (hb : d82763 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d82764 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d75630 q = 1) (hb : d82765 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d82766 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11174 (p : Pattern) (ha : d75630 p = 1) (hb : d82772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d82767 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11173 q ha hb
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d82768 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82769 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82770 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82771 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82772 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11175 (p : Pattern) (ha : d75630 p = 1) (hb : d82777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6267 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6268 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6268, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6268, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6269 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6270 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6271 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d82777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro11176 (p : Pattern) (ha : d75630 p = 1) (hb : d82788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d82783 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82784 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d82784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75630, d82784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82785 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82786 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82787 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d82788 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11177 (p : Pattern) (ha : d75630 p = 1) (hb : d82794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6273 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11072 q ha hb
    | true =>
      simp only [d6273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11073 q ha hb
  have h2 (q : Pattern) (ha : d6274 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82775 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d82775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82776 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82778 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11175 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82779 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d82780 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d82781 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d82782 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d82789 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11176 q ha hb
  have h11 (q : Pattern) (ha : d75630 q = 1) (hb : d82790 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d75630 q = 1) (hb : d82791 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d82792 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d75630 q = 1) (hb : d82793 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d82794 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11178 (p : Pattern) (ha : d75630 p = 1) (hb : d82800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d82795 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11177 q ha hb
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d82796 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82797 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82798 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82799 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82800 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11179 (p : Pattern) (ha : d75630 p = 1) (hb : d82806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6413 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6414 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6414, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6414, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6415 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6416 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6417 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d82806 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro11180 (p : Pattern) (ha : d75630 p = 1) (hb : d82817 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d82812 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82813 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d82813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75630, d82813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82814 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82815 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82816 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d82817 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11181 (p : Pattern) (ha : d75630 p = 1) (hb : d82823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6419 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11084 q ha hb
    | true =>
      simp only [d6419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11085 q ha hb
  have h2 (q : Pattern) (ha : d6420 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82804 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d82804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82805 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82807 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11179 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82808 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d82809 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d82810 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d82811 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d82818 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11180 q ha hb
  have h11 (q : Pattern) (ha : d75630 q = 1) (hb : d82819 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d75630 q = 1) (hb : d82820 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d82821 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d75630 q = 1) (hb : d82822 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d82823 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11182 (p : Pattern) (ha : d75630 p = 1) (hb : d82829 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d82824 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11181 q ha hb
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d82825 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82826 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82827 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82828 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82829 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11183 (p : Pattern) (ha : d75630 p = 1) (hb : d82836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6560 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6561 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6561, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6561, d75630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6562 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6563 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6564 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d82836 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro11184 (p : Pattern) (ha : d75630 p = 1) (hb : d82847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d82842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82843 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75630, d82843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75630, d82843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82844 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82846 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d82847 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11185 (p : Pattern) (ha : d75630 p = 1) (hb : d82853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6566 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11096 q ha hb
    | true =>
      simp only [d6566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11097 q ha hb
  have h2 (q : Pattern) (ha : d6567 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82834 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d82834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82835 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11183 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82838 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d82839 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d82840 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d82841 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d82848 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11184 q ha hb
  have h11 (q : Pattern) (ha : d75630 q = 1) (hb : d82849 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d75630 q = 1) (hb : d82850 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d82851 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d75630 q = 1) (hb : d82852 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d82853 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro11186 (p : Pattern) (ha : d75630 p = 1) (hb : d82859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d82854 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11185 q ha hb
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d82855 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82856 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82857 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82858 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82859 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11187 (p : Pattern) (ha : d75630 p = 1) (hb : d82865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d75630 q = 1) (hb : d82746 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11166 q ha hb
    | true =>
      simp only [d82746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11170 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d82773 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11174 q ha hb
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82774 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82801 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11178 q ha hb
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82802 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82803 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75630 q = 1) (hb : d82830 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11182 q ha hb
  have h8 (q : Pattern) (ha : d75630 q = 1) (hb : d82831 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75630 q = 1) (hb : d82832 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75630 q = 1) (hb : d82833 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d82833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75630 q = 1) (hb : d82860 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11186 q ha hb
  have h12 (q : Pattern) (ha : d75630 q = 1) (hb : d82861 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d75630 q = 1) (hb : d82862 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d75630 q = 1) (hb : d82863 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d82863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75630 q = 1) (hb : d82864 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d82864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d75630 q = 1) (hb : d82865 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d82865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro11188 (p : Pattern) (ha : d75630 p = 1) (hb : d82871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d82866 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d82866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11187 q ha hb
    | true =>
      simp only [d82866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d82867 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d82867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82868 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d82868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82869 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d82869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82870 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d82870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82871 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d82871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11189 (p : Pattern) (ha : d75630 p = 1) (hb : d82877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d82872 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d82872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11188 q ha hb
    | true =>
      simp only [d82872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d82873 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d82873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82874 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d82874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82875 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d82875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82876 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d82876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82877 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d82877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11190 (p : Pattern) (ha : d75630 p = 1) (hb : d82883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d82878 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d82878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11189 q ha hb
    | true =>
      simp only [d82878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d82879 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d82879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82880 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d82880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82881 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d82881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82882 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d82882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82883 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d82883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11191 (p : Pattern) (ha : d75630 p = 1) (hb : d82889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d82884 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d82884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11190 q ha hb
    | true =>
      simp only [d82884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d82885 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d82885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82886 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d82886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82887 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d82887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82888 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d82888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82889 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d82889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11192 (p : Pattern) (ha : d75630 p = 1) (hb : d82895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d82890 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d82890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11191 q ha hb
    | true =>
      simp only [d82890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d82891 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d82891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82892 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d82892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82893 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d82893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82894 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d82894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82895 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d82895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11193 (p : Pattern) (ha : d75630 p = 1) (hb : d82901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d82896 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d82896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11192 q ha hb
    | true =>
      simp only [d82896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d82897 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d82897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82898 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d82898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82899 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d82899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82900 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d82900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82901 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d82901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11194 (p : Pattern) (ha : d75630 p = 1) (hb : d82907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75630 q = 1) (hb : d82902 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d82902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11193 q ha hb
    | true =>
      simp only [d82902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d75630 q = 1) (hb : d82903 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d82903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d75630 q = 1) (hb : d82904 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d82904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d75630 q = 1) (hb : d82905 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d82905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75630 q = 1) (hb : d82906 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d82906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d75630 q = 1) (hb : d82907 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d82907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro11195 (p : Pattern) (ha : d150 p = 1) (hb : d92313 p = 1) : d6739 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d147 q = 1) : d147 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148 q = 1) (hb : d92313 q = 1) : d475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d92313, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148, d92313, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d34 q = 1) (hb : d92313 q = 1) : d34 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d149 q = 1) (hb : d92313 q = 1) : d6738 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d6738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d149, d6738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d150 q = 1) (hb : d92313 q = 1) : d6739 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, d6739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150, d6739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11196 (p : Pattern) (ha : d4736 p = 1) (hb : d92314 p = 1) : d8334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d151 q = 1) (hb : d92313 q = 1) : d6740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d6740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11195 q ha hb
    | true =>
      simp only [d151, d6740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152 q = 1) (hb : d92313 q = 1) : d6741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d6741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d152, d6741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4733 q = 1) (hb : d92314 q = 1) : d8331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4733, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4734 q = 1) (hb : d92314 q = 1) : d8332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d8332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4734, d8332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4735 q = 1) (hb : d92314 q = 1) : d8333 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d8333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4735, d8333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4736 q = 1) (hb : d92314 q = 1) : d8334 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, d8334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, d8334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11197 (p : Pattern) (ha : d76787 p = 1) (hb : d92314 p = 1) : d93275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d92314 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d92314 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d92314 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5850 q = 1) (hb : d92314 q = 1) : d93270 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11196 q ha hb
    | true =>
      simp only [d5850, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76783 q = 1) (hb : d92314 q = 1) : d93271 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76783, d93271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76783, d93271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d92314 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d76784 q = 1) (hb : d92314 q = 1) : d93272 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76784, d93272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76784, d93272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76785 q = 1) (hb : d92314 q = 1) : d93273 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76785, d93273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76785, d93273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76786 q = 1) (hb : d92314 q = 1) : d93274 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76786, d93274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76786, d93274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76787 q = 1) (hb : d92314 q = 1) : d93275 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76787, d93275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76787, d93275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro11198 (p : Pattern) (ha : d5355 p = 1) (hb : d92314 p = 1) : d8355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d92313 q = 1) : d6740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d6740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11195 q ha hb
    | true =>
      simp only [d151, d6740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d92313 q = 1) : d6741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d6741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d6741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4733 q = 1) (hb : d92314 q = 1) : d8331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4734 q = 1) (hb : d92314 q = 1) : d8332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d8332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4734, d8332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4735 q = 1) (hb : d92314 q = 1) : d8333 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d8333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4735, d8333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d5355 q = 1) (hb : d92314 q = 1) : d8355 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d8355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5355, d8355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11199 (p : Pattern) (ha : d76792 p = 1) (hb : d92314 p = 1) : d93281 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d92314 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d92314 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d92314 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5850 q = 1) (hb : d92314 q = 1) : d93270 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11196 q ha hb
    | true =>
      simp only [d5850, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76783 q = 1) (hb : d92314 q = 1) : d93271 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76783, d93271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76783, d93271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d92314 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d76784 q = 1) (hb : d92314 q = 1) : d93272 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76784, d93272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76784, d93272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76785 q = 1) (hb : d92314 q = 1) : d93273 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76785, d93273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76785, d93273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76786 q = 1) (hb : d92314 q = 1) : d93274 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76786, d93274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76786, d93274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d92314 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d92314 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d92314 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d5856 q = 1) (hb : d92314 q = 1) : d93276 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5856, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11198 q ha hb
    | true =>
      simp only [d5856, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76788 q = 1) (hb : d92314 q = 1) : d93277 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76788, d93277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76788, d93277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d92314 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d76789 q = 1) (hb : d92314 q = 1) : d93278 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76789, d93278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76789, d93278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76790 q = 1) (hb : d92314 q = 1) : d93279 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76790, d93279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76790, d93279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76791 q = 1) (hb : d92314 q = 1) : d93280 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76791, d93280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76791, d93280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d76792 q = 1) (hb : d92314 q = 1) : d93281 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76792, d93281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76792, d93281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro11200 (p : Pattern) (ha : d76799 p = 1) (hb : d92314 p = 1) : d93288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d92314 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5856 q = 1) (hb : d92314 q = 1) : d93276 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5856, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11198 q ha hb
    | true =>
      simp only [d5856, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76788 q = 1) (hb : d92314 q = 1) : d93277 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76788, d93277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76788, d93277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d92314 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76789 q = 1) (hb : d92314 q = 1) : d93278 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76789, d93278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76789, d93278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76797 q = 1) (hb : d92314 q = 1) : d93286 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76797, d93286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76797, d93286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76798 q = 1) (hb : d92314 q = 1) : d93287 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76798, d93287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76798, d93287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76799 q = 1) (hb : d92314 q = 1) : d93288 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76799, d93288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76799, d93288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11201 (p : Pattern) (ha : d237 p = 1) (hb : d92313 p = 1) : d6772 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d234 q = 1) : d234 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d235 q = 1) (hb : d92313 q = 1) : d673 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d92313, d673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d235, d92313, d673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d75 q = 1) (hb : d92313 q = 1) : d75 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d236 q = 1) (hb : d92313 q = 1) : d6771 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d6771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d236, d6771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d237 q = 1) (hb : d92313 q = 1) : d6772 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d6772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237, d6772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11202 (p : Pattern) (ha : d5377 p = 1) (hb : d92314 p = 1) : d8398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d92313 q = 1) : d6773 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d6773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11201 q ha hb
    | true =>
      simp only [d238, d6773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d92313 q = 1) : d6774 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d6774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d6774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5374 q = 1) (hb : d92314 q = 1) : d8395 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, d92314, d8395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, d92314, d8395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5375 q = 1) (hb : d92314 q = 1) : d8396 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, d8396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5375, d8396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5376 q = 1) (hb : d92314 q = 1) : d8397 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, d8397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5376, d8397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d5377 q = 1) (hb : d92314 q = 1) : d8398 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, d8398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5377, d8398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11203 (p : Pattern) (ha : d76809 p = 1) (hb : d92314 p = 1) : d93299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d92314 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5874 q = 1) (hb : d92314 q = 1) : d93294 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5874, d93294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11202 q ha hb
    | true =>
      simp only [d5874, d93294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76805 q = 1) (hb : d92314 q = 1) : d93295 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76805, d93295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76805, d93295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d92314 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76806 q = 1) (hb : d92314 q = 1) : d93296 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76806, d93296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76806, d93296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76807 q = 1) (hb : d92314 q = 1) : d93297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76807, d93297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76807, d93297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76808 q = 1) (hb : d92314 q = 1) : d93298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76808, d93298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76808, d93298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76809 q = 1) (hb : d92314 q = 1) : d93299 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76809, d93299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76809, d93299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11204 (p : Pattern) (ha : d76815 p = 1) (hb : d92314 p = 1) : d93305 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d92314 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76793 q = 1) (hb : d92314 q = 1) : d93282 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76793, d93282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11197 q ha hb
    | true =>
      simp only [d76793, d93282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11199 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d92314 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76794 q = 1) (hb : d92314 q = 1) : d93283 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76794, d93283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76794, d93283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76795 q = 1) (hb : d92314 q = 1) : d93284 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76795, d93284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76795, d93284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76796 q = 1) (hb : d92314 q = 1) : d93285 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76796, d93285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76796, d93285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76800 q = 1) (hb : d92314 q = 1) : d93289 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76800, d93289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76800, d93289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11200 q ha hb
  have h8 (q : Pattern) (ha : d76801 q = 1) (hb : d92314 q = 1) : d93290 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76801, d93290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76801, d93290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d76802 q = 1) (hb : d92314 q = 1) : d93291 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76802, d93291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76802, d93291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d76803 q = 1) (hb : d92314 q = 1) : d93292 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76803, d93292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76803, d93292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d76804 q = 1) (hb : d92314 q = 1) : d93293 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76804, d93293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76804, d93293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d76810 q = 1) (hb : d92314 q = 1) : d93300 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76810, d93300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76810, d93300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11203 q ha hb
  have h13 (q : Pattern) (ha : d76811 q = 1) (hb : d92314 q = 1) : d93301 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76811, d93301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76811, d93301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d76812 q = 1) (hb : d92314 q = 1) : d93302 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76812, d93302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76812, d93302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d76813 q = 1) (hb : d92314 q = 1) : d93303 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76813, d93303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76813, d93303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d76814 q = 1) (hb : d92314 q = 1) : d93304 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76814, d93304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76814, d93304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d76815 q = 1) (hb : d92314 q = 1) : d93305 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76815, d93305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76815, d93305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro11205 (p : Pattern) (ha : d5895 p = 1) (hb : d92314 p = 1) : d93315 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d92314 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5850 q = 1) (hb : d92314 q = 1) : d93270 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11196 q ha hb
    | true =>
      simp only [d5850, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5891 q = 1) (hb : d92314 q = 1) : d93311 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5891, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5892 q = 1) (hb : d92314 q = 1) : d93312 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5892, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5893 q = 1) (hb : d92314 q = 1) : d93313 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5893, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5894 q = 1) (hb : d92314 q = 1) : d93314 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5894, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5895 q = 1) (hb : d92314 q = 1) : d93315 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5895, d93315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5895, d93315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11206 (p : Pattern) (ha : d5902 p = 1) (hb : d92314 p = 1) : d93322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d92314 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5850 q = 1) (hb : d92314 q = 1) : d93270 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11196 q ha hb
    | true =>
      simp only [d5850, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5891 q = 1) (hb : d92314 q = 1) : d93311 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5891, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5892 q = 1) (hb : d92314 q = 1) : d93312 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5892, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5893 q = 1) (hb : d92314 q = 1) : d93313 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5893, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5894 q = 1) (hb : d92314 q = 1) : d93314 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5894, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d92314 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5856 q = 1) (hb : d92314 q = 1) : d93276 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5856, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11198 q ha hb
    | true =>
      simp only [d5856, d93276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5898 q = 1) (hb : d92314 q = 1) : d93318 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5898, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5898, d93318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5899 q = 1) (hb : d92314 q = 1) : d93319 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5899, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5899, d93319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5900 q = 1) (hb : d92314 q = 1) : d93320 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5900, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5900, d93320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5901 q = 1) (hb : d92314 q = 1) : d93321 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5901, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5901, d93321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5902 q = 1) (hb : d92314 q = 1) : d93322 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5902, d93322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5902, d93322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro11207 (p : Pattern) (ha : d5952 p = 1) (hb : d92314 p = 1) : d93360 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d92314 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5850 q = 1) (hb : d92314 q = 1) : d93270 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11196 q ha hb
    | true =>
      simp only [d5850, d93270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5891 q = 1) (hb : d92314 q = 1) : d93311 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5891, d93311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5892 q = 1) (hb : d92314 q = 1) : d93312 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5892, d93312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5893 q = 1) (hb : d92314 q = 1) : d93313 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5893, d93313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5894 q = 1) (hb : d92314 q = 1) : d93314 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5894, d93314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d92314 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5952 q = 1) (hb : d92314 q = 1) : d93360 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5952, d93360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5952, d93360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11208 (p : Pattern) (ha : d5907 p = 1) (hb : d92314 p = 1) : d93327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d151 q = 1) (hb : d92313 q = 1) : d6740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d6740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11195 q ha hb
    | true =>
      simp only [d151, d6740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152 q = 1) (hb : d92313 q = 1) : d6741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d6741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d152, d6741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4733 q = 1) (hb : d92314 q = 1) : d8331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4733, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4734 q = 1) (hb : d92314 q = 1) : d8332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d8332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4734, d8332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5906 q = 1) (hb : d92314 q = 1) : d93326 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5906, d93326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5906, d93326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5907 q = 1) (hb : d92314 q = 1) : d93327 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5907, d93327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5907, d93327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11209 (p : Pattern) (ha : d5914 p = 1) (hb : d92314 p = 1) : d93334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d151 q = 1) (hb : d92313 q = 1) : d6740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d6740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11195 q ha hb
    | true =>
      simp only [d151, d6740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152 q = 1) (hb : d92313 q = 1) : d6741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d6741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d152, d6741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4733 q = 1) (hb : d92314 q = 1) : d8331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4733, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5912 q = 1) (hb : d92314 q = 1) : d93332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5912, d93332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5912, d93332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5913 q = 1) (hb : d92314 q = 1) : d93333 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5913, d93333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5913, d93333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5914 q = 1) (hb : d92314 q = 1) : d93334 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5914, d93334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5914, d93334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11210 (p : Pattern) (ha : d330 p = 1) (hb : d92313 p = 1) : d8313 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d327 q = 1) : d327 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d328 q = 1) (hb : d92313 q = 1) : d6797 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, d92313, d6797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d328, d92313, d6797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d147 q = 1) : d147 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148 q = 1) (hb : d92313 q = 1) : d475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d92313, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d148, d92313, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d329 q = 1) (hb : d92313 q = 1) : d8312 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d329, d8312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d329, d8312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d330 q = 1) (hb : d92313 q = 1) : d8313 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d330, d8313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d330, d8313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11211 (p : Pattern) (ha : d5921 p = 1) (hb : d92314 p = 1) : d8479 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d331 q = 1) (hb : d92313 q = 1) : d8314 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d331, d8314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11210 q ha hb
    | true =>
      simp only [d331, d8314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d332 q = 1) (hb : d92313 q = 1) : d8315 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d332, d8315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d332, d8315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5918 q = 1) (hb : d92314 q = 1) : d8476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5918, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5918, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5919 q = 1) (hb : d92314 q = 1) : d8477 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5919, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5919, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5920 q = 1) (hb : d92314 q = 1) : d8478 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5920, d8478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5920, d8478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5921 q = 1) (hb : d92314 q = 1) : d8479 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5921, d8479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5921, d8479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11212 (p : Pattern) (ha : d76825 p = 1) (hb : d92314 p = 1) : d93343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d92314 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5908 q = 1) (hb : d92314 q = 1) : d93328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5908, d93328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11208 q ha hb
    | true =>
      simp only [d5908, d93328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5909 q = 1) (hb : d92314 q = 1) : d93329 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5909, d93329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5909, d93329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5910 q = 1) (hb : d92314 q = 1) : d93330 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5910, d93330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5910, d93330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5911 q = 1) (hb : d92314 q = 1) : d93331 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5911, d93331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5911, d93331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d92314 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5915 q = 1) (hb : d92314 q = 1) : d93335 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5915, d93335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11209 q ha hb
    | true =>
      simp only [d5915, d93335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5916 q = 1) (hb : d92314 q = 1) : d93336 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5916, d93336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5916, d93336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5917 q = 1) (hb : d92314 q = 1) : d93337 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5917, d93337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5917, d93337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5922 q = 1) (hb : d92314 q = 1) : d93338 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5922, d93338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11211 q ha hb
    | true =>
      simp only [d5922, d93338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11196 q ha hb
  have h11 (q : Pattern) (ha : d76821 q = 1) (hb : d92314 q = 1) : d93339 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76821, d93339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76821, d93339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d92314 q = 1) : d8335 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d8335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11196 q ha hb
    | true =>
      simp only [d4737, d8335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d92314 q = 1) : d8336 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d8336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d8336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d76822 q = 1) (hb : d92314 q = 1) : d93340 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76822, d93340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76822, d93340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76823 q = 1) (hb : d92314 q = 1) : d93341 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76823, d93341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76823, d93341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76824 q = 1) (hb : d92314 q = 1) : d93342 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76824, d93342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76824, d93342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76825 q = 1) (hb : d92314 q = 1) : d93343 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76825, d93343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76825, d93343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro11213 (p : Pattern) (ha : d5933 p = 1) (hb : d92314 p = 1) : d93344 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d151 q = 1) (hb : d92313 q = 1) : d6740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d6740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11195 q ha hb
    | true =>
      simp only [d151, d6740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152 q = 1) (hb : d92313 q = 1) : d6741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d6741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d152, d6741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4733 q = 1) (hb : d92314 q = 1) : d8331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4733, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4734 q = 1) (hb : d92314 q = 1) : d8332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d8332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4734, d8332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5906 q = 1) (hb : d92314 q = 1) : d93326 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5906, d93326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5906, d93326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5933 q = 1) (hb : d92314 q = 1) : d93344 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5933, d93344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5933, d93344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro11214 (p : Pattern) (ha : d5938 p = 1) (hb : d92314 p = 1) : d93349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d151 q = 1) (hb : d92313 q = 1) : d6740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d6740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11195 q ha hb
    | true =>
      simp only [d151, d6740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152 q = 1) (hb : d92313 q = 1) : d6741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d6741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d152, d6741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4733 q = 1) (hb : d92314 q = 1) : d8331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4733, d92314, d8331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5912 q = 1) (hb : d92314 q = 1) : d93332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5912, d93332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5912, d93332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5913 q = 1) (hb : d92314 q = 1) : d93333 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5913, d93333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5913, d93333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5938 q = 1) (hb : d92314 q = 1) : d93349 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5938, d93349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5938, d93349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro11215 (p : Pattern) (ha : d5942 p = 1) (hb : d92314 p = 1) : d8501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331 q = 1) (hb : d92313 q = 1) : d8314 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d331, d8314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11210 q ha hb
    | true =>
      simp only [d331, d8314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d332 q = 1) (hb : d92313 q = 1) : d8315 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d332, d8315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d332, d8315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5918 q = 1) (hb : d92314 q = 1) : d8476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5918, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5918, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5919 q = 1) (hb : d92314 q = 1) : d8477 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5919, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5919, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5920 q = 1) (hb : d92314 q = 1) : d8478 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5920, d8478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5920, d8478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d5942 q = 1) (hb : d92314 q = 1) : d8501 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5942, d8501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5942, d8501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11216 (p : Pattern) (ha : d76830 p = 1) (hb : d92314 p = 1) : d93358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d92314 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5908 q = 1) (hb : d92314 q = 1) : d93328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5908, d93328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11208 q ha hb
    | true =>
      simp only [d5908, d93328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5909 q = 1) (hb : d92314 q = 1) : d93329 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5909, d93329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5909, d93329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5910 q = 1) (hb : d92314 q = 1) : d93330 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5910, d93330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5910, d93330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5911 q = 1) (hb : d92314 q = 1) : d93331 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5911, d93331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5911, d93331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d92314 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5915 q = 1) (hb : d92314 q = 1) : d93335 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5915, d93335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11209 q ha hb
    | true =>
      simp only [d5915, d93335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5916 q = 1) (hb : d92314 q = 1) : d93336 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5916, d93336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5916, d93336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5917 q = 1) (hb : d92314 q = 1) : d93337 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5917, d93337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5917, d93337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5922 q = 1) (hb : d92314 q = 1) : d93338 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5922, d93338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11211 q ha hb
    | true =>
      simp only [d5922, d93338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11196 q ha hb
  have h11 (q : Pattern) (ha : d76821 q = 1) (hb : d92314 q = 1) : d93339 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76821, d93339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76821, d93339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d92314 q = 1) : d8335 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d8335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11196 q ha hb
    | true =>
      simp only [d4737, d8335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d92314 q = 1) : d8336 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d8336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d8336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d76822 q = 1) (hb : d92314 q = 1) : d93340 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76822, d93340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76822, d93340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76823 q = 1) (hb : d92314 q = 1) : d93341 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76823, d93341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76823, d93341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76824 q = 1) (hb : d92314 q = 1) : d93342 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76824, d93342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76824, d93342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d92314 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d5934 q = 1) (hb : d92314 q = 1) : d93345 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5934, d93345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11213 q ha hb
    | true =>
      simp only [d5934, d93345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5935 q = 1) (hb : d92314 q = 1) : d93346 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5935, d93346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5935, d93346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d5936 q = 1) (hb : d92314 q = 1) : d93347 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5936, d93347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d5936, d93347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d5937 q = 1) (hb : d92314 q = 1) : d93348 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5937, d93348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5937, d93348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d92314 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d5939 q = 1) (hb : d92314 q = 1) : d93350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5939, d93350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11214 q ha hb
    | true =>
      simp only [d5939, d93350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d5940 q = 1) (hb : d92314 q = 1) : d93351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5940, d93351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5940, d93351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d5941 q = 1) (hb : d92314 q = 1) : d93352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5941, d93352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5941, d93352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d5943 q = 1) (hb : d92314 q = 1) : d93353 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5943, d93353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11215 q ha hb
    | true =>
      simp only [d5943, d93353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11198 q ha hb
  have h27 (q : Pattern) (ha : d76826 q = 1) (hb : d92314 q = 1) : d93354 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76826, d93354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d76826, d93354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d5356 q = 1) (hb : d92314 q = 1) : d8356 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d8356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11198 q ha hb
    | true =>
      simp only [d5356, d8356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d5357 q = 1) (hb : d92314 q = 1) : d8357 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d8357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d5357, d8357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d76827 q = 1) (hb : d92314 q = 1) : d93355 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76827, d93355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d76827, d93355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d76828 q = 1) (hb : d92314 q = 1) : d93356 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76828, d93356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d76828, d93356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d76829 q = 1) (hb : d92314 q = 1) : d93357 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76829, d93357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76829, d93357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d76830 q = 1) (hb : d92314 q = 1) : d93358 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76830, d93358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76830, d93358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro11217 (p : Pattern) (ha : d76837 p = 1) (hb : d92314 p = 1) : d93367 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5943 q = 1) (hb : d92314 q = 1) : d93353 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5943, d93353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11215 q ha hb
    | true =>
      simp only [d5943, d93353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11198 q ha hb
  have h2 (q : Pattern) (ha : d76826 q = 1) (hb : d92314 q = 1) : d93354 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76826, d93354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76826, d93354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d92314 q = 1) : d8356 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d8356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11198 q ha hb
    | true =>
      simp only [d5356, d8356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5357 q = 1) (hb : d92314 q = 1) : d8357 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d8357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5357, d8357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76827 q = 1) (hb : d92314 q = 1) : d93355 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76827, d93355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76827, d93355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76835 q = 1) (hb : d92314 q = 1) : d93365 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76835, d93365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76835, d93365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76836 q = 1) (hb : d92314 q = 1) : d93366 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76836, d93366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76836, d93366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76837 q = 1) (hb : d92314 q = 1) : d93367 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76837, d93367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76837, d93367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11218 (p : Pattern) (ha : d423 p = 1) (hb : d92313 p = 1) : d8377 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d420 q = 1) : d420 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d234 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d421 q = 1) (hb : d92313 q = 1) : d6843 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d92313, d6843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d421, d92313, d6843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d234 q = 1) : d234 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d235 q = 1) (hb : d92313 q = 1) : d673 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d92313, d673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d235, d92313, d673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d422 q = 1) (hb : d92313 q = 1) : d8376 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d422, d8376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d422, d8376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d423 q = 1) (hb : d92313 q = 1) : d8377 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d423, d8377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d423, d8377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11219 (p : Pattern) (ha : d5968 p = 1) (hb : d92314 p = 1) : d8555 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d424 q = 1) (hb : d92313 q = 1) : d8378 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d424, d8378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11218 q ha hb
    | true =>
      simp only [d424, d8378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d425 q = 1) (hb : d92313 q = 1) : d8379 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d425, d8379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d425, d8379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5965 q = 1) (hb : d92314 q = 1) : d8552 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5965, d92314, d8552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5965, d92314, d8552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5966 q = 1) (hb : d92314 q = 1) : d8553 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5966, d8553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5966, d8553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5967 q = 1) (hb : d92314 q = 1) : d8554 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5967, d8554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5967, d8554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d5968 q = 1) (hb : d92314 q = 1) : d8555 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5968, d8555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5968, d8555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11220 (p : Pattern) (ha : d76847 p = 1) (hb : d92314 p = 1) : d93378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5969 q = 1) (hb : d92314 q = 1) : d93373 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5969, d93373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11219 q ha hb
    | true =>
      simp only [d5969, d93373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11202 q ha hb
  have h2 (q : Pattern) (ha : d76843 q = 1) (hb : d92314 q = 1) : d93374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76843, d93374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76843, d93374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d92314 q = 1) : d8399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d8399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11202 q ha hb
    | true =>
      simp only [d5378, d8399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d92314 q = 1) : d8400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d8400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5379, d8400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76844 q = 1) (hb : d92314 q = 1) : d93375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76844, d93375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76844, d93375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76845 q = 1) (hb : d92314 q = 1) : d93376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76845, d93376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76845, d93376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76846 q = 1) (hb : d92314 q = 1) : d93377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76846, d93377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76846, d93377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76847 q = 1) (hb : d92314 q = 1) : d93378 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76847, d93378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76847, d93378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11221 (p : Pattern) (ha : d76853 p = 1) (hb : d92314 p = 1) : d93384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5896 q = 1) (hb : d92314 q = 1) : d93316 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5896, d93316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5896, d93316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11205 q ha hb
  have h2 (q : Pattern) (ha : d5897 q = 1) (hb : d92314 q = 1) : d93317 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5897, d93317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5897, d93317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5903 q = 1) (hb : d92314 q = 1) : d93323 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5903, d93323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11205 q ha hb
    | true =>
      simp only [d5903, d93323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11206 q ha hb
  have h4 (q : Pattern) (ha : d5904 q = 1) (hb : d92314 q = 1) : d93324 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5904, d93324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5904, d93324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5905 q = 1) (hb : d92314 q = 1) : d93325 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d5905, d93325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5905, d93325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76831 q = 1) (hb : d92314 q = 1) : d93359 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76831, d93359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11212 q ha hb
    | true =>
      simp only [d76831, d93359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11216 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d92314 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5953 q = 1) (hb : d92314 q = 1) : d93361 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5953, d93361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11207 q ha hb
    | true =>
      simp only [d5953, d93361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76832 q = 1) (hb : d92314 q = 1) : d93362 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76832, d93362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76832, d93362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76833 q = 1) (hb : d92314 q = 1) : d93363 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76833, d93363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76833, d93363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d76834 q = 1) (hb : d92314 q = 1) : d93364 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76834, d93364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76834, d93364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d76838 q = 1) (hb : d92314 q = 1) : d93368 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76838, d93368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76838, d93368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11217 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d92314 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d76839 q = 1) (hb : d92314 q = 1) : d93369 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76839, d93369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76839, d93369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76840 q = 1) (hb : d92314 q = 1) : d93370 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76840, d93370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76840, d93370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d76841 q = 1) (hb : d92314 q = 1) : d93371 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76841, d93371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76841, d93371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d76842 q = 1) (hb : d92314 q = 1) : d93372 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76842, d93372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76842, d93372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76848 q = 1) (hb : d92314 q = 1) : d93379 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76848, d93379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76848, d93379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11220 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d92314 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d76849 q = 1) (hb : d92314 q = 1) : d93380 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76849, d93380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d76849, d93380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d76850 q = 1) (hb : d92314 q = 1) : d93381 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76850, d93381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76850, d93381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d76851 q = 1) (hb : d92314 q = 1) : d93382 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76851, d93382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76851, d93382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d76852 q = 1) (hb : d92314 q = 1) : d93383 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76852, d93383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76852, d93383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d76853 q = 1) (hb : d92314 q = 1) : d93384 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76853, d93384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76853, d93384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro11222 (p : Pattern) (ha : d76859 p = 1) (hb : d92314 p = 1) : d93390 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d92314 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d76816 q = 1) (hb : d92314 q = 1) : d93306 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76816, d93306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76816, d93306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11204 q ha hb
  have h3 (q : Pattern) (ha : d76817 q = 1) (hb : d92314 q = 1) : d93307 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76817, d93307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76817, d93307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76818 q = 1) (hb : d92314 q = 1) : d93308 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76818, d93308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76818, d93308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76819 q = 1) (hb : d92314 q = 1) : d93309 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76819, d93309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76819, d93309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76820 q = 1) (hb : d92314 q = 1) : d93310 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76820, d93310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76820, d93310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76854 q = 1) (hb : d92314 q = 1) : d93385 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76854, d93385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76854, d93385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11221 q ha hb
  have h8 (q : Pattern) (ha : d76855 q = 1) (hb : d92314 q = 1) : d93386 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76855, d93386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76855, d93386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76856 q = 1) (hb : d92314 q = 1) : d93387 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76856, d93387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76856, d93387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76857 q = 1) (hb : d92314 q = 1) : d93388 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76857, d93388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76857, d93388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76858 q = 1) (hb : d92314 q = 1) : d93389 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76858, d93389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76858, d93389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d76859 q = 1) (hb : d92314 q = 1) : d93390 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76859, d93390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76859, d93390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro11223 (p : Pattern) (ha : d477 p = 1) (hb : d92313 p = 1) : d8313 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d327 q = 1) : d327 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d328 q = 1) (hb : d92313 q = 1) : d6797 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, d92313, d6797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d328, d92313, d6797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d475 q = 1) (hb : d92313 q = 1) : d475 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d476 q = 1) (hb : d92313 q = 1) : d8312 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d476, d8312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d476, d8312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d477 q = 1) (hb : d92313 q = 1) : d8313 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d477, d8313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d477, d8313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11224 (p : Pattern) (ha : d5399 p = 1) (hb : d92314 p = 1) : d8479 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d478 q = 1) (hb : d92313 q = 1) : d8314 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d8314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11223 q ha hb
    | true =>
      simp only [d478, d8314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d479 q = 1) (hb : d92313 q = 1) : d8315 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d8315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d479, d8315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5396 q = 1) (hb : d92314 q = 1) : d8476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5396, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5397 q = 1) (hb : d92314 q = 1) : d8477 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5397, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5397, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5398 q = 1) (hb : d92314 q = 1) : d8478 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5398, d8478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5398, d8478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5399 q = 1) (hb : d92314 q = 1) : d8479 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5399, d8479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5399, d8479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11225 (p : Pattern) (ha : d5997 p = 1) (hb : d92314 p = 1) : d93396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d92314 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5992 q = 1) (hb : d92314 q = 1) : d93391 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5992, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11224 q ha hb
    | true =>
      simp only [d5992, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5993 q = 1) (hb : d92314 q = 1) : d93392 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5993, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5993, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5994 q = 1) (hb : d92314 q = 1) : d93393 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5994, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5994, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5995 q = 1) (hb : d92314 q = 1) : d93394 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5995, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5995, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5996 q = 1) (hb : d92314 q = 1) : d93395 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5996, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5996, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5997 q = 1) (hb : d92314 q = 1) : d93396 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5997, d93396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5997, d93396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro11226 (p : Pattern) (ha : d5406 p = 1) (hb : d92314 p = 1) : d8501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d92313 q = 1) : d8314 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d8314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11223 q ha hb
    | true =>
      simp only [d478, d8314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d92313 q = 1) : d8315 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d8315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d8315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5396 q = 1) (hb : d92314 q = 1) : d8476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5396, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5397 q = 1) (hb : d92314 q = 1) : d8477 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5397, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5397, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5398 q = 1) (hb : d92314 q = 1) : d8478 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5398, d8478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5398, d8478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d5406 q = 1) (hb : d92314 q = 1) : d8501 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5406, d8501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5406, d8501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11227 (p : Pattern) (ha : d6005 p = 1) (hb : d92314 p = 1) : d93404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d92314 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5992 q = 1) (hb : d92314 q = 1) : d93391 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5992, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11224 q ha hb
    | true =>
      simp only [d5992, d93391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5993 q = 1) (hb : d92314 q = 1) : d93392 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5993, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5993, d93392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5994 q = 1) (hb : d92314 q = 1) : d93393 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5994, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5994, d93393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5995 q = 1) (hb : d92314 q = 1) : d93394 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5995, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5995, d93394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5996 q = 1) (hb : d92314 q = 1) : d93395 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5996, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5996, d93395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d501 q = 1) (hb : d92314 q = 1) : d501 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6000 q = 1) (hb : d92314 q = 1) : d93399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6000, d93399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11226 q ha hb
    | true =>
      simp only [d6000, d93399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6001 q = 1) (hb : d92314 q = 1) : d93400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6001, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6001, d93400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6002 q = 1) (hb : d92314 q = 1) : d93401 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6002, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6002, d93401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6003 q = 1) (hb : d92314 q = 1) : d93402 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6003, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6003, d93402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6004 q = 1) (hb : d92314 q = 1) : d93403 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6004, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6004, d93403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6005 q = 1) (hb : d92314 q = 1) : d93404 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6005, d93404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6005, d93404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro11228 (p : Pattern) (ha : d4824 p = 1) (hb : d92313 p = 1) : d6799 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d327 q = 1) : d327 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d328 q = 1) (hb : d92313 q = 1) : d6797 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, d92313, d6797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d328, d92313, d6797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d4822 q = 1) (hb : d92313 q = 1) : d4822 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4823 q = 1) (hb : d92313 q = 1) : d6798 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d4823, d6798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4823, d6798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4824 q = 1) (hb : d92313 q = 1) : d6799 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d4824, d6799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4824, d6799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11229 (p : Pattern) (ha : d4830 p = 1) (hb : d92314 p = 1) : d93427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4825 q = 1) (hb : d92313 q = 1) : d6800 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4825, d6800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11228 q ha hb
    | true =>
      simp only [d4825, d6800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4826 q = 1) (hb : d92313 q = 1) : d6801 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4826, d6801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4826, d6801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4827 q = 1) (hb : d92314 q = 1) : d93424 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4827, d92314, d93424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4827, d92314, d93424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4828 q = 1) (hb : d92314 q = 1) : d93425 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4828, d93425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4828, d93425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4829 q = 1) (hb : d92314 q = 1) : d93426 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4829, d93426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4829, d93426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4830 q = 1) (hb : d92314 q = 1) : d93427 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4830, d93427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4830, d93427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11230 (p : Pattern) (ha : d6061 p = 1) (hb : d92314 p = 1) : d93457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d92314 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6056 q = 1) (hb : d92314 q = 1) : d93452 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6056, d93452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11229 q ha hb
    | true =>
      simp only [d6056, d93452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6057 q = 1) (hb : d92314 q = 1) : d93453 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6057, d93453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6057, d93453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6058 q = 1) (hb : d92314 q = 1) : d93454 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6058, d93454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6058, d93454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6059 q = 1) (hb : d92314 q = 1) : d93455 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6059, d93455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6059, d93455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6060 q = 1) (hb : d92314 q = 1) : d93456 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6060, d93456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6060, d93456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d637 q = 1) (hb : d92314 q = 1) : d637 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6061 q = 1) (hb : d92314 q = 1) : d93457 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6061, d93457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6061, d93457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11231 (p : Pattern) (ha : d6010 p = 1) (hb : d92314 p = 1) : d93409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d478 q = 1) (hb : d92313 q = 1) : d8314 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d8314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11223 q ha hb
    | true =>
      simp only [d478, d8314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d479 q = 1) (hb : d92313 q = 1) : d8315 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d8315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d479, d8315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5396 q = 1) (hb : d92314 q = 1) : d8476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5396, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5397 q = 1) (hb : d92314 q = 1) : d8477 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5397, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5397, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6009 q = 1) (hb : d92314 q = 1) : d93408 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6009, d93408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6009, d93408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6010 q = 1) (hb : d92314 q = 1) : d93409 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6010, d93409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6010, d93409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11232 (p : Pattern) (ha : d6017 p = 1) (hb : d92314 p = 1) : d93416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d478 q = 1) (hb : d92313 q = 1) : d8314 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d8314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11223 q ha hb
    | true =>
      simp only [d478, d8314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d479 q = 1) (hb : d92313 q = 1) : d8315 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d8315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d479, d8315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5396 q = 1) (hb : d92314 q = 1) : d8476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5396, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6015 q = 1) (hb : d92314 q = 1) : d93414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6015, d93414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6015, d93414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6016 q = 1) (hb : d92314 q = 1) : d93415 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6016, d93415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6016, d93415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6017 q = 1) (hb : d92314 q = 1) : d93416 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6017, d93416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6017, d93416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11233 (p : Pattern) (ha : d554 p = 1) (hb : d92313 p = 1) : d8453 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d551 q = 1) : d551 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d327 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d552 q = 1) (hb : d92313 q = 1) : d8451 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d552, d92313, d8451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d552, d92313, d8451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d327 q = 1) : d327 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d328 q = 1) (hb : d92313 q = 1) : d6797 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, d92313, d6797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d328, d92313, d6797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d553 q = 1) (hb : d92313 q = 1) : d8452 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d553, d8452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d553, d8452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d554 q = 1) (hb : d92313 q = 1) : d8453 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d554, d8453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d554, d8453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11234 (p : Pattern) (ha : d6024 p = 1) (hb : d92314 p = 1) : d93423 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d555 q = 1) (hb : d92313 q = 1) : d8454 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d555, d8454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11233 q ha hb
    | true =>
      simp only [d555, d8454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d556 q = 1) (hb : d92313 q = 1) : d8455 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d556, d8455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d556, d8455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6021 q = 1) (hb : d92314 q = 1) : d93420 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6021, d92314, d93420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6021, d92314, d93420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6022 q = 1) (hb : d92314 q = 1) : d93421 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6022, d93421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6022, d93421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6023 q = 1) (hb : d92314 q = 1) : d93422 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6023, d93422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6023, d93422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6024 q = 1) (hb : d92314 q = 1) : d93423 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6024, d93423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6024, d93423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11235 (p : Pattern) (ha : d76864 p = 1) (hb : d92314 p = 1) : d93433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d514 q = 1) (hb : d92314 q = 1) : d514 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6011 q = 1) (hb : d92314 q = 1) : d93410 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6011, d93410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11231 q ha hb
    | true =>
      simp only [d6011, d93410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6012 q = 1) (hb : d92314 q = 1) : d93411 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6012, d93411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6012, d93411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6013 q = 1) (hb : d92314 q = 1) : d93412 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6013, d93412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6013, d93412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6014 q = 1) (hb : d92314 q = 1) : d93413 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6014, d93413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6014, d93413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d92314 q = 1) : d524 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6018 q = 1) (hb : d92314 q = 1) : d93417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6018, d93417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11232 q ha hb
    | true =>
      simp only [d6018, d93417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6019 q = 1) (hb : d92314 q = 1) : d93418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6019, d93418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6019, d93418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6020 q = 1) (hb : d92314 q = 1) : d93419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6020, d93419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6020, d93419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6025 q = 1) (hb : d92314 q = 1) : d93428 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6025, d93428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11234 q ha hb
    | true =>
      simp only [d6025, d93428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11229 q ha hb
  have h11 (q : Pattern) (ha : d76860 q = 1) (hb : d92314 q = 1) : d93429 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76860, d93429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76860, d93429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5400 q = 1) (hb : d92314 q = 1) : d8480 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d8480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11224 q ha hb
    | true =>
      simp only [d5400, d8480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5401 q = 1) (hb : d92314 q = 1) : d8481 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5401, d8481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5401, d8481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d76861 q = 1) (hb : d92314 q = 1) : d93430 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76861, d93430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76861, d93430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76862 q = 1) (hb : d92314 q = 1) : d93431 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76862, d93431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76862, d93431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76863 q = 1) (hb : d92314 q = 1) : d93432 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76863, d93432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76863, d93432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76864 q = 1) (hb : d92314 q = 1) : d93433 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76864, d93433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76864, d93433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro11236 (p : Pattern) (ha : d6036 p = 1) (hb : d92314 p = 1) : d93434 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d478 q = 1) (hb : d92313 q = 1) : d8314 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d8314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11223 q ha hb
    | true =>
      simp only [d478, d8314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d479 q = 1) (hb : d92313 q = 1) : d8315 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d8315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d479, d8315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5396 q = 1) (hb : d92314 q = 1) : d8476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5396, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5397 q = 1) (hb : d92314 q = 1) : d8477 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5397, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5397, d8477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6009 q = 1) (hb : d92314 q = 1) : d93408 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6009, d93408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6009, d93408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6036 q = 1) (hb : d92314 q = 1) : d93434 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6036, d93434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6036, d93434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro11237 (p : Pattern) (ha : d6041 p = 1) (hb : d92314 p = 1) : d93439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d478 q = 1) (hb : d92313 q = 1) : d8314 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d8314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11223 q ha hb
    | true =>
      simp only [d478, d8314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d479 q = 1) (hb : d92313 q = 1) : d8315 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d8315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d479, d8315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5396 q = 1) (hb : d92314 q = 1) : d8476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5396, d92314, d8476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6015 q = 1) (hb : d92314 q = 1) : d93414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6015, d93414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6015, d93414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6016 q = 1) (hb : d92314 q = 1) : d93415 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6016, d93415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6016, d93415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6041 q = 1) (hb : d92314 q = 1) : d93439 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6041, d93439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6041, d93439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro11238 (p : Pattern) (ha : d6045 p = 1) (hb : d92314 p = 1) : d93443 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d555 q = 1) (hb : d92313 q = 1) : d8454 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d555, d8454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11233 q ha hb
    | true =>
      simp only [d555, d8454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d556 q = 1) (hb : d92313 q = 1) : d8455 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d556, d8455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d556, d8455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6021 q = 1) (hb : d92314 q = 1) : d93420 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6021, d92314, d93420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6021, d92314, d93420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6022 q = 1) (hb : d92314 q = 1) : d93421 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6022, d93421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6022, d93421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6023 q = 1) (hb : d92314 q = 1) : d93422 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6023, d93422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6023, d93422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6045 q = 1) (hb : d92314 q = 1) : d93443 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6045, d93443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6045, d93443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11239 (p : Pattern) (ha : d6046 p = 1) (hb : d92314 p = 1) : d93444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4825 q = 1) (hb : d92313 q = 1) : d6800 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4825, d6800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11228 q ha hb
    | true =>
      simp only [d4825, d6800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4826 q = 1) (hb : d92313 q = 1) : d6801 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4826, d6801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4826, d6801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4827 q = 1) (hb : d92314 q = 1) : d93424 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4827, d92314, d93424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4827, d92314, d93424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4828 q = 1) (hb : d92314 q = 1) : d93425 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4828, d93425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4828, d93425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4829 q = 1) (hb : d92314 q = 1) : d93426 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4829, d93426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4829, d93426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6046 q = 1) (hb : d92314 q = 1) : d93444 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6046, d93444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6046, d93444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11240 (p : Pattern) (ha : d76869 p = 1) (hb : d92314 p = 1) : d93450 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d514 q = 1) (hb : d92314 q = 1) : d514 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6011 q = 1) (hb : d92314 q = 1) : d93410 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6011, d93410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11231 q ha hb
    | true =>
      simp only [d6011, d93410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6012 q = 1) (hb : d92314 q = 1) : d93411 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6012, d93411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6012, d93411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6013 q = 1) (hb : d92314 q = 1) : d93412 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6013, d93412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6013, d93412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6014 q = 1) (hb : d92314 q = 1) : d93413 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6014, d93413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6014, d93413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d92314 q = 1) : d524 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6018 q = 1) (hb : d92314 q = 1) : d93417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6018, d93417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11232 q ha hb
    | true =>
      simp only [d6018, d93417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6019 q = 1) (hb : d92314 q = 1) : d93418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6019, d93418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6019, d93418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6020 q = 1) (hb : d92314 q = 1) : d93419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6020, d93419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6020, d93419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6025 q = 1) (hb : d92314 q = 1) : d93428 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6025, d93428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11234 q ha hb
    | true =>
      simp only [d6025, d93428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11229 q ha hb
  have h11 (q : Pattern) (ha : d76860 q = 1) (hb : d92314 q = 1) : d93429 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76860, d93429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76860, d93429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5400 q = 1) (hb : d92314 q = 1) : d8480 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d8480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11224 q ha hb
    | true =>
      simp only [d5400, d8480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5401 q = 1) (hb : d92314 q = 1) : d8481 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5401, d8481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5401, d8481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d76861 q = 1) (hb : d92314 q = 1) : d93430 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76861, d93430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76861, d93430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76862 q = 1) (hb : d92314 q = 1) : d93431 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76862, d93431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76862, d93431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76863 q = 1) (hb : d92314 q = 1) : d93432 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76863, d93432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76863, d93432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d610 q = 1) (hb : d92314 q = 1) : d610 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d6037 q = 1) (hb : d92314 q = 1) : d93435 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6037, d93435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11236 q ha hb
    | true =>
      simp only [d6037, d93435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d6038 q = 1) (hb : d92314 q = 1) : d93436 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6038, d93436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6038, d93436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6039 q = 1) (hb : d92314 q = 1) : d93437 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6039, d93437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d6039, d93437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d6040 q = 1) (hb : d92314 q = 1) : d93438 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6040, d93438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6040, d93438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d616 q = 1) (hb : d92314 q = 1) : d616 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d6042 q = 1) (hb : d92314 q = 1) : d93440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6042, d93440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11237 q ha hb
    | true =>
      simp only [d6042, d93440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d6043 q = 1) (hb : d92314 q = 1) : d93441 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6043, d93441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6043, d93441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d6044 q = 1) (hb : d92314 q = 1) : d93442 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6044, d93442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d6044, d93442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d6047 q = 1) (hb : d92314 q = 1) : d93445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6047, d93445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11238 q ha hb
    | true =>
      simp only [d6047, d93445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11239 q ha hb
  have h27 (q : Pattern) (ha : d76865 q = 1) (hb : d92314 q = 1) : d93446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76865, d93446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d76865, d93446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d5407 q = 1) (hb : d92314 q = 1) : d8502 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d8502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11226 q ha hb
    | true =>
      simp only [d5407, d8502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d5408 q = 1) (hb : d92314 q = 1) : d8503 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5408, d8503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d5408, d8503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d76866 q = 1) (hb : d92314 q = 1) : d93447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76866, d93447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d76866, d93447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d76867 q = 1) (hb : d92314 q = 1) : d93448 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76867, d93448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d76867, d93448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d76868 q = 1) (hb : d92314 q = 1) : d93449 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76868, d93449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76868, d93449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d76869 q = 1) (hb : d92314 q = 1) : d93450 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76869, d93450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76869, d93450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro11241 (p : Pattern) (ha : d76876 p = 1) (hb : d92314 p = 1) : d93464 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6047 q = 1) (hb : d92314 q = 1) : d93445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6047, d93445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11238 q ha hb
    | true =>
      simp only [d6047, d93445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11239 q ha hb
  have h2 (q : Pattern) (ha : d76865 q = 1) (hb : d92314 q = 1) : d93446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76865, d93446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76865, d93446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5407 q = 1) (hb : d92314 q = 1) : d8502 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d8502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11226 q ha hb
    | true =>
      simp only [d5407, d8502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5408 q = 1) (hb : d92314 q = 1) : d8503 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5408, d8503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5408, d8503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76866 q = 1) (hb : d92314 q = 1) : d93447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76866, d93447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76866, d93447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76874 q = 1) (hb : d92314 q = 1) : d93462 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76874, d93462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76874, d93462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76875 q = 1) (hb : d92314 q = 1) : d93463 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76875, d93463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76875, d93463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76876 q = 1) (hb : d92314 q = 1) : d93464 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76876, d93464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76876, d93464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11242 (p : Pattern) (ha : d675 p = 1) (hb : d92313 p = 1) : d8377 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d420 q = 1) : d420 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d234 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d421 q = 1) (hb : d92313 q = 1) : d6843 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d92313, d6843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d421, d92313, d6843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d673 q = 1) (hb : d92313 q = 1) : d673 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d674 q = 1) (hb : d92313 q = 1) : d8376 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d674, d8376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d674, d8376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d675 q = 1) (hb : d92313 q = 1) : d8377 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d675, d8377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d675, d8377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11243 (p : Pattern) (ha : d5428 p = 1) (hb : d92314 p = 1) : d8555 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d676 q = 1) (hb : d92313 q = 1) : d8378 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d676, d8378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11242 q ha hb
    | true =>
      simp only [d676, d8378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d677 q = 1) (hb : d92313 q = 1) : d8379 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d677, d8379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d677, d8379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5425 q = 1) (hb : d92314 q = 1) : d8552 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5425, d92314, d8552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5425, d92314, d8552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5426 q = 1) (hb : d92314 q = 1) : d8553 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5426, d8553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5426, d8553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5427 q = 1) (hb : d92314 q = 1) : d8554 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5427, d8554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5427, d8554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d5428 q = 1) (hb : d92314 q = 1) : d8555 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5428, d8555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5428, d8555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11244 (p : Pattern) (ha : d670 p = 1) (hb : d92313 p = 1) : d8529 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d667 q = 1) : d667 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d420 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d668 q = 1) (hb : d92313 q = 1) : d8527 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d668, d92313, d8527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d668, d92313, d8527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d420 q = 1) : d420 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d234 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d421 q = 1) (hb : d92313 q = 1) : d6843 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d92313, d6843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d421, d92313, d6843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d669 q = 1) (hb : d92313 q = 1) : d8528 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d669, d8528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d669, d8528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d670 q = 1) (hb : d92313 q = 1) : d8529 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d670, d8529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d670, d8529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11245 (p : Pattern) (ha : d6077 p = 1) (hb : d92314 p = 1) : d93473 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d671 q = 1) (hb : d92313 q = 1) : d8530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d671, d8530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11244 q ha hb
    | true =>
      simp only [d671, d8530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d672 q = 1) (hb : d92313 q = 1) : d8531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d672, d8531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d672, d8531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6074 q = 1) (hb : d92314 q = 1) : d93470 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6074, d92314, d93470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6074, d92314, d93470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6075 q = 1) (hb : d92314 q = 1) : d93471 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6075, d93471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6075, d93471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6076 q = 1) (hb : d92314 q = 1) : d93472 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6076, d93472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6076, d93472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6077 q = 1) (hb : d92314 q = 1) : d93473 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6077, d93473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6077, d93473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11246 (p : Pattern) (ha : d6084 p = 1) (hb : d92313 p = 1) : d6845 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d420 q = 1) : d420 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d234 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d421 q = 1) (hb : d92313 q = 1) : d6843 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d92313, d6843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d421, d92313, d6843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d6082 q = 1) (hb : d92313 q = 1) : d6082 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6083 q = 1) (hb : d92313 q = 1) : d6844 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6083, d6844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6083, d6844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6084 q = 1) (hb : d92313 q = 1) : d6845 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6084, d6845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6084, d6845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro11247 (p : Pattern) (ha : d6090 p = 1) (hb : d92314 p = 1) : d93477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6085 q = 1) (hb : d92313 q = 1) : d6846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6085, d6846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11246 q ha hb
    | true =>
      simp only [d6085, d6846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6086 q = 1) (hb : d92313 q = 1) : d6847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6086, d6847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6086, d6847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6087 q = 1) (hb : d92314 q = 1) : d93474 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6087, d92314, d93474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6087, d92314, d93474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6088 q = 1) (hb : d92314 q = 1) : d93475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6088, d93475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6088, d93475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6089 q = 1) (hb : d92314 q = 1) : d93476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6089, d93476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6089, d93476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6090 q = 1) (hb : d92314 q = 1) : d93477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6090, d93477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6090, d93477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro11248 (p : Pattern) (ha : d76886 p = 1) (hb : d92314 p = 1) : d93483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6091 q = 1) (hb : d92314 q = 1) : d93478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6091, d93478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11245 q ha hb
    | true =>
      simp only [d6091, d93478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11247 q ha hb
  have h2 (q : Pattern) (ha : d76882 q = 1) (hb : d92314 q = 1) : d93479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76882, d93479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76882, d93479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5429 q = 1) (hb : d92314 q = 1) : d8556 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5429, d8556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11243 q ha hb
    | true =>
      simp only [d5429, d8556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5430 q = 1) (hb : d92314 q = 1) : d8557 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5430, d8557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5430, d8557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76883 q = 1) (hb : d92314 q = 1) : d93480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76883, d93480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76883, d93480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76884 q = 1) (hb : d92314 q = 1) : d93481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76884, d93481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76884, d93481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76885 q = 1) (hb : d92314 q = 1) : d93482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76885, d93482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76885, d93482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76886 q = 1) (hb : d92314 q = 1) : d93483 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76886, d93483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76886, d93483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro11249 (p : Pattern) (ha : d76892 p = 1) (hb : d92314 p = 1) : d93489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5998 q = 1) (hb : d92314 q = 1) : d93397 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5998, d93397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5998, d93397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11225 q ha hb
  have h2 (q : Pattern) (ha : d5999 q = 1) (hb : d92314 q = 1) : d93398 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5999, d93398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5999, d93398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6006 q = 1) (hb : d92314 q = 1) : d93405 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6006, d93405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11225 q ha hb
    | true =>
      simp only [d6006, d93405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11227 q ha hb
  have h4 (q : Pattern) (ha : d6007 q = 1) (hb : d92314 q = 1) : d93406 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6007, d93406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6007, d93406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6008 q = 1) (hb : d92314 q = 1) : d93407 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6008, d93407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6008, d93407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76870 q = 1) (hb : d92314 q = 1) : d93451 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76870, d93451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11235 q ha hb
    | true =>
      simp only [d76870, d93451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11240 q ha hb
  have h7 (q : Pattern) (ha : d644 q = 1) (hb : d92314 q = 1) : d644 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6062 q = 1) (hb : d92314 q = 1) : d93458 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6062, d93458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11230 q ha hb
    | true =>
      simp only [d6062, d93458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76871 q = 1) (hb : d92314 q = 1) : d93459 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76871, d93459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76871, d93459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76872 q = 1) (hb : d92314 q = 1) : d93460 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76872, d93460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76872, d93460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d76873 q = 1) (hb : d92314 q = 1) : d93461 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76873, d93461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76873, d93461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d76877 q = 1) (hb : d92314 q = 1) : d93465 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76877, d93465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76877, d93465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11241 q ha hb
  have h13 (q : Pattern) (ha : d654 q = 1) (hb : d92314 q = 1) : d654 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d76878 q = 1) (hb : d92314 q = 1) : d93466 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76878, d93466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76878, d93466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76879 q = 1) (hb : d92314 q = 1) : d93467 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76879, d93467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76879, d93467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d76880 q = 1) (hb : d92314 q = 1) : d93468 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76880, d93468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76880, d93468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d76881 q = 1) (hb : d92314 q = 1) : d93469 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76881, d93469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76881, d93469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76887 q = 1) (hb : d92314 q = 1) : d93484 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76887, d93484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76887, d93484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11248 q ha hb
  have h19 (q : Pattern) (ha : d737 q = 1) (hb : d92314 q = 1) : d737 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d76888 q = 1) (hb : d92314 q = 1) : d93485 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76888, d93485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d76888, d93485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d76889 q = 1) (hb : d92314 q = 1) : d93486 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76889, d93486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76889, d93486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d76890 q = 1) (hb : d92314 q = 1) : d93487 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76890, d93487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76890, d93487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d76891 q = 1) (hb : d92314 q = 1) : d93488 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76891, d93488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76891, d93488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d76892 q = 1) (hb : d92314 q = 1) : d93489 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76892, d93489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76892, d93489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
end NetHack.Soko22Hazard87
