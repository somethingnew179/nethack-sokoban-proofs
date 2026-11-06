import NetHack.Soko22Hazard87.AndIntroBlocks0175
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro44000 (p : Pattern) (ha : d189791 p = 1) (hb : d190398 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189786 q = 1) (hb : d190393 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d189786, d190393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43999 q ha hb
    | true =>
      simp only [d189786, d190393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189787 q = 1) (hb : d190394 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d189787, d190394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189787, d190394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d189788 q = 1) (hb : d190395 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d189788, d190395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189788, d190395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189789 q = 1) (hb : d190396 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d189789, d190396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189789, d190396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189790 q = 1) (hb : d190397 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d189790, d190397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189790, d190397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189791 q = 1) (hb : d190398 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d189791, d190398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189791, d190398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44001 (p : Pattern) (ha : d189797 p = 1) (hb : d190404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189792 q = 1) (hb : d190399 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d189792, d190399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44000 q ha hb
    | true =>
      simp only [d189792, d190399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189793 q = 1) (hb : d190400 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d189793, d190400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189793, d190400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d189794 q = 1) (hb : d190401 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d189794, d190401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189794, d190401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189795 q = 1) (hb : d190402 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d189795, d190402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189795, d190402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189796 q = 1) (hb : d190403 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d189796, d190403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189796, d190403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189797 q = 1) (hb : d190404 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d189797, d190404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189797, d190404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44002 (p : Pattern) (ha : d189803 p = 1) (hb : d190410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189798 q = 1) (hb : d190405 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d189798, d190405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44001 q ha hb
    | true =>
      simp only [d189798, d190405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189799 q = 1) (hb : d190406 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d189799, d190406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189799, d190406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d189800 q = 1) (hb : d190407 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d189800, d190407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189800, d190407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189801 q = 1) (hb : d190408 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d189801, d190408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189801, d190408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189802 q = 1) (hb : d190409 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d189802, d190409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189802, d190409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189803 q = 1) (hb : d190410 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d189803, d190410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189803, d190410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44003 (p : Pattern) (ha : d189809 p = 1) (hb : d190416 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189804 q = 1) (hb : d190411 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d189804, d190411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44002 q ha hb
    | true =>
      simp only [d189804, d190411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189805 q = 1) (hb : d190412 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d189805, d190412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189805, d190412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d189806 q = 1) (hb : d190413 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d189806, d190413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189806, d190413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189807 q = 1) (hb : d190414 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d189807, d190414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189807, d190414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189808 q = 1) (hb : d190415 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d189808, d190415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189808, d190415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189809 q = 1) (hb : d190416 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d189809, d190416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189809, d190416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44004 (p : Pattern) (ha : d189881 p = 1) (hb : d190421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d188779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d189817 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d189877 q = 1) (hb : d190417 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189877, d190417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189877, d190417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d188755 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d189878 q = 1) (hb : d190418 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189878, d190418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189878, d190418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189879 q = 1) (hb : d190419 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189879, d190419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d189879, d190419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d189880 q = 1) (hb : d190420 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189880, d190420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d189880, d190420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d189881 q = 1) (hb : d190421 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189881, d190421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d189881, d190421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44005 (p : Pattern) (ha : d190225 p = 1) (hb : d190427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189882 q = 1) (hb : d190422 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189882, d190422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d189882, d190422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44004 q ha hb
  have h2 (q : Pattern) (ha : d190221 q = 1) (hb : d190423 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d190221, d190423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190221, d190423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d190222 q = 1) (hb : d190424 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d190222, d190424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d190222, d190424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d190223 q = 1) (hb : d190425 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d190223, d190425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190223, d190425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d190224 q = 1) (hb : d190426 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d190224, d190426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d190224, d190426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d190225 q = 1) (hb : d190427 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d190225, d190427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190225, d190427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44006 (p : Pattern) (ha : d190235 p = 1) (hb : d190437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d188815 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d189840 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d190231 q = 1) (hb : d190433 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190231, d190433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190231, d190433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d188832 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d190232 q = 1) (hb : d190434 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190232, d190434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190232, d190434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d190233 q = 1) (hb : d190435 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d190233, d190435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190233, d190435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d190234 q = 1) (hb : d190436 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d190234, d190436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190234, d190436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d190235 q = 1) (hb : d190437 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d190235, d190437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190235, d190437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44007 (p : Pattern) (ha : d190241 p = 1) (hb : d190443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190236 q = 1) (hb : d190438 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d190236, d190438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190236, d190438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44006 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d188843 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d190237 q = 1) (hb : d190439 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d190237, d190439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190237, d190439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d190238 q = 1) (hb : d190440 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d190238, d190440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190238, d190440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d190239 q = 1) (hb : d190441 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d190239, d190441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d190239, d190441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d190240 q = 1) (hb : d190442 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d190240, d190442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d190240, d190442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d190241 q = 1) (hb : d190443 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d190241, d190443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190241, d190443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44008 (p : Pattern) (ha : d190247 p = 1) (hb : d190449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188769 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d190226 q = 1) (hb : d190428 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d190226, d190428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190226, d190428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44005 q ha hb
  have h3 (q : Pattern) (ha : d190227 q = 1) (hb : d190429 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d190227, d190429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190227, d190429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d190228 q = 1) (hb : d190430 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d190228, d190430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190228, d190430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d190229 q = 1) (hb : d190431 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d190229, d190431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190229, d190431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d190230 q = 1) (hb : d190432 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d190230, d190432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190230, d190432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d190242 q = 1) (hb : d190444 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d190242, d190444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190242, d190444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44007 q ha hb
  have h8 (q : Pattern) (ha : d190243 q = 1) (hb : d190445 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d190243, d190445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190243, d190445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d190244 q = 1) (hb : d190446 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d190244, d190446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190244, d190446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d190245 q = 1) (hb : d190447 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d190245, d190447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190245, d190447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d190246 q = 1) (hb : d190448 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d190246, d190448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190246, d190448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d190247 q = 1) (hb : d190449 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d190247, d190449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d190247, d190449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro44009 (p : Pattern) (ha : d190253 p = 1) (hb : d190454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d188876 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d190248 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d190249 q = 1) (hb : d190450 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190249, d190450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190249, d190450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d188901 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d190250 q = 1) (hb : d190451 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190250, d190451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190250, d190451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d190251 q = 1) (hb : d190452 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d190251, d190452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190251, d190452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d190252 q = 1) (hb : d190453 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d190252, d190453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190252, d190453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d190253 q = 1) (hb : d190454 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d190253, d190454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190253, d190454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44010 (p : Pattern) (ha : d190259 p = 1) (hb : d190460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190254 q = 1) (hb : d190455 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d190254, d190455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190254, d190455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44009 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d188917 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d190255 q = 1) (hb : d190456 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d190255, d190456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190255, d190456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d190256 q = 1) (hb : d190457 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d190256, d190457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190256, d190457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d190257 q = 1) (hb : d190458 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d190257, d190458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d190257, d190458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d190258 q = 1) (hb : d190459 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d190258, d190459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d190258, d190459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d190259 q = 1) (hb : d190460 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d190259, d190460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190259, d190460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44011 (p : Pattern) (ha : d190265 p = 1) (hb : d190466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190260 q = 1) (hb : d190461 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d190260, d190461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190260, d190461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44010 q ha hb
  have h2 (q : Pattern) (ha : d190261 q = 1) (hb : d190462 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d190261, d190462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190261, d190462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d190262 q = 1) (hb : d190463 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d190262, d190463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190262, d190463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d190263 q = 1) (hb : d190464 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d190263, d190464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190263, d190464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d190264 q = 1) (hb : d190465 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d190264, d190465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190264, d190465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d190265 q = 1) (hb : d190466 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d190265, d190466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190265, d190466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44012 (p : Pattern) (ha : d190272 p = 1) (hb : d190472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d188954 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d190267 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d190268 q = 1) (hb : d190468 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190268, d190468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190268, d190468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d188980 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d190269 q = 1) (hb : d190469 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190269, d190469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190269, d190469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d190270 q = 1) (hb : d190470 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d190270, d190470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190270, d190470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d190271 q = 1) (hb : d190471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d190271, d190471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190271, d190471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d190272 q = 1) (hb : d190472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d190272, d190472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190272, d190472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44013 (p : Pattern) (ha : d190278 p = 1) (hb : d190478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190273 q = 1) (hb : d190473 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d190273, d190473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190273, d190473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44012 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d188996 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d190274 q = 1) (hb : d190474 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d190274, d190474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190274, d190474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d190275 q = 1) (hb : d190475 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d190275, d190475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190275, d190475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d190276 q = 1) (hb : d190476 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d190276, d190476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d190276, d190476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d190277 q = 1) (hb : d190477 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d190277, d190477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d190277, d190477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d190278 q = 1) (hb : d190478 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d190278, d190478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190278, d190478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44014 (p : Pattern) (ha : d190284 p = 1) (hb : d190484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190279 q = 1) (hb : d190479 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d190279, d190479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190279, d190479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44013 q ha hb
  have h2 (q : Pattern) (ha : d190280 q = 1) (hb : d190480 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d190280, d190480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190280, d190480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d190281 q = 1) (hb : d190481 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d190281, d190481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190281, d190481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d190282 q = 1) (hb : d190482 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d190282, d190482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190282, d190482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d190283 q = 1) (hb : d190483 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d190283, d190483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190283, d190483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d190284 q = 1) (hb : d190484 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d190284, d190484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190284, d190484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44015 (p : Pattern) (ha : d190299 p = 1) (hb : d190491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d189036 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d190294 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d190295 q = 1) (hb : d190487 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190295, d190487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190295, d190487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d189068 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d190296 q = 1) (hb : d190488 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190296, d190488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190296, d190488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d190297 q = 1) (hb : d190489 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d190297, d190489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190297, d190489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d190298 q = 1) (hb : d190490 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d190298, d190490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190298, d190490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d190299 q = 1) (hb : d190491 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d190299, d190491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190299, d190491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44016 (p : Pattern) (ha : d190305 p = 1) (hb : d190497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190300 q = 1) (hb : d190492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d190300, d190492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190300, d190492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44015 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d189084 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d190301 q = 1) (hb : d190493 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d190301, d190493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190301, d190493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d190302 q = 1) (hb : d190494 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d190302, d190494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190302, d190494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d190303 q = 1) (hb : d190495 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d190303, d190495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d190303, d190495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d190304 q = 1) (hb : d190496 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d190304, d190496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d190304, d190496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d190305 q = 1) (hb : d190497 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d190305, d190497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190305, d190497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44017 (p : Pattern) (ha : d190311 p = 1) (hb : d190503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190306 q = 1) (hb : d190498 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d190306, d190498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190306, d190498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44016 q ha hb
  have h2 (q : Pattern) (ha : d190307 q = 1) (hb : d190499 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d190307, d190499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190307, d190499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d190308 q = 1) (hb : d190500 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d190308, d190500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190308, d190500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d190309 q = 1) (hb : d190501 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d190309, d190501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190309, d190501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d190310 q = 1) (hb : d190502 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d190310, d190502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190310, d190502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d190311 q = 1) (hb : d190503 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d190311, d190503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190311, d190503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44018 (p : Pattern) (ha : d190327 p = 1) (hb : d190511 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d189125 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d190322 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d190323 q = 1) (hb : d190507 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190323, d190507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190323, d190507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d189157 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d190324 q = 1) (hb : d190508 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190324, d190508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190324, d190508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d190325 q = 1) (hb : d190509 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d190325, d190509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190325, d190509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d190326 q = 1) (hb : d190510 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d190326, d190510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190326, d190510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d190327 q = 1) (hb : d190511 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d190327, d190511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190327, d190511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44019 (p : Pattern) (ha : d190333 p = 1) (hb : d190517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190328 q = 1) (hb : d190512 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d190328, d190512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190328, d190512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44018 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d189173 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d190329 q = 1) (hb : d190513 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d190329, d190513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190329, d190513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d190330 q = 1) (hb : d190514 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d190330, d190514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190330, d190514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d190331 q = 1) (hb : d190515 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d190331, d190515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d190331, d190515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d190332 q = 1) (hb : d190516 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d190332, d190516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d190332, d190516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d190333 q = 1) (hb : d190517 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d190333, d190517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190333, d190517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44020 (p : Pattern) (ha : d190339 p = 1) (hb : d190523 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190334 q = 1) (hb : d190518 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d190334, d190518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190334, d190518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44019 q ha hb
  have h2 (q : Pattern) (ha : d190335 q = 1) (hb : d190519 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d190335, d190519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190335, d190519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d190336 q = 1) (hb : d190520 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d190336, d190520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190336, d190520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d190337 q = 1) (hb : d190521 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d190337, d190521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190337, d190521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d190338 q = 1) (hb : d190522 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d190338, d190522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190338, d190522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d190339 q = 1) (hb : d190523 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d190339, d190523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190339, d190523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44021 (p : Pattern) (ha : d190356 p = 1) (hb : d190532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d189215 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d190351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d190352 q = 1) (hb : d190528 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190352, d190528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190352, d190528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d189247 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d190353 q = 1) (hb : d190529 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190353, d190529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190353, d190529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d190354 q = 1) (hb : d190530 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d190354, d190530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190354, d190530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d190355 q = 1) (hb : d190531 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d190355, d190531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190355, d190531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d190356 q = 1) (hb : d190532 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d190356, d190532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190356, d190532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44022 (p : Pattern) (ha : d190362 p = 1) (hb : d190538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190357 q = 1) (hb : d190533 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d190357, d190533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190357, d190533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44021 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d189263 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d190358 q = 1) (hb : d190534 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d190358, d190534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190358, d190534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d190359 q = 1) (hb : d190535 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d190359, d190535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190359, d190535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d190360 q = 1) (hb : d190536 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d190360, d190536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d190360, d190536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d190361 q = 1) (hb : d190537 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d190361, d190537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d190361, d190537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d190362 q = 1) (hb : d190538 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d190362, d190538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190362, d190538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44023 (p : Pattern) (ha : d190368 p = 1) (hb : d190544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190363 q = 1) (hb : d190539 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d190363, d190539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190363, d190539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44022 q ha hb
  have h2 (q : Pattern) (ha : d190364 q = 1) (hb : d190540 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d190364, d190540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190364, d190540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d190365 q = 1) (hb : d190541 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d190365, d190541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190365, d190541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d190366 q = 1) (hb : d190542 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d190366, d190542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190366, d190542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d190367 q = 1) (hb : d190543 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d190367, d190543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190367, d190543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d190368 q = 1) (hb : d190544 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d190368, d190544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190368, d190544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44024 (p : Pattern) (ha : d190374 p = 1) (hb : d190550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d190266 q = 1) (hb : d190467 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d190266, d190467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44008 q ha hb
    | true =>
      simp only [d190266, d190467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44011 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d190285 q = 1) (hb : d190485 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d190285, d190485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190285, d190485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44014 q ha hb
  have h3 (q : Pattern) (ha : d190286 q = 1) (hb : d190486 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d190286, d190486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d190286, d190486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d190312 q = 1) (hb : d190504 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d190312, d190504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190312, d190504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44017 q ha hb
  have h5 (q : Pattern) (ha : d190313 q = 1) (hb : d190505 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d190313, d190505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190313, d190505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d190314 q = 1) (hb : d190506 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d190314, d190506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190314, d190506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d190340 q = 1) (hb : d190524 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d190340, d190524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190340, d190524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44020 q ha hb
  have h8 (q : Pattern) (ha : d190341 q = 1) (hb : d190525 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d190341, d190525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190341, d190525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d190342 q = 1) (hb : d190526 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d190342, d190526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190342, d190526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d190343 q = 1) (hb : d190527 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d190343, d190527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d190343, d190527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d190369 q = 1) (hb : d190545 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d190369, d190545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190369, d190545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44023 q ha hb
  have h12 (q : Pattern) (ha : d190370 q = 1) (hb : d190546 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d190370, d190546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190370, d190546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d190371 q = 1) (hb : d190547 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d190371, d190547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190371, d190547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d190372 q = 1) (hb : d190548 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d190372, d190548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190372, d190548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d190373 q = 1) (hb : d190549 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d190373, d190549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d190373, d190549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d190374 q = 1) (hb : d190550 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d190374, d190550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d190374, d190550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro44025 (p : Pattern) (ha : d190380 p = 1) (hb : d190556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190375 q = 1) (hb : d190551 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d190375, d190551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44024 q ha hb
    | true =>
      simp only [d190375, d190551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d190376 q = 1) (hb : d190552 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d190376, d190552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190376, d190552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d190377 q = 1) (hb : d190553 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d190377, d190553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d190377, d190553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d190378 q = 1) (hb : d190554 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d190378, d190554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190378, d190554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d190379 q = 1) (hb : d190555 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d190379, d190555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d190379, d190555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d190380 q = 1) (hb : d190556 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d190380, d190556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d190380, d190556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44026 (p : Pattern) (ha : d190386 p = 1) (hb : d190562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190381 q = 1) (hb : d190557 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d190381, d190557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44025 q ha hb
    | true =>
      simp only [d190381, d190557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d190382 q = 1) (hb : d190558 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d190382, d190558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190382, d190558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d190383 q = 1) (hb : d190559 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d190383, d190559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d190383, d190559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d190384 q = 1) (hb : d190560 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d190384, d190560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190384, d190560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d190385 q = 1) (hb : d190561 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d190385, d190561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d190385, d190561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d190386 q = 1) (hb : d190562 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d190386, d190562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d190386, d190562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44027 (p : Pattern) (ha : d190392 p = 1) (hb : d190568 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190387 q = 1) (hb : d190563 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d190387, d190563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44026 q ha hb
    | true =>
      simp only [d190387, d190563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d190388 q = 1) (hb : d190564 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d190388, d190564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190388, d190564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d190389 q = 1) (hb : d190565 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d190389, d190565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d190389, d190565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d190390 q = 1) (hb : d190566 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d190390, d190566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190390, d190566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d190391 q = 1) (hb : d190567 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d190391, d190567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d190391, d190567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d190392 q = 1) (hb : d190568 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d190392, d190568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d190392, d190568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44028 (p : Pattern) (ha : d190398 p = 1) (hb : d190574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190393 q = 1) (hb : d190569 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d190393, d190569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44027 q ha hb
    | true =>
      simp only [d190393, d190569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d190394 q = 1) (hb : d190570 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d190394, d190570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190394, d190570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d190395 q = 1) (hb : d190571 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d190395, d190571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d190395, d190571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d190396 q = 1) (hb : d190572 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d190396, d190572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190396, d190572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d190397 q = 1) (hb : d190573 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d190397, d190573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d190397, d190573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d190398 q = 1) (hb : d190574 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d190398, d190574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d190398, d190574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44029 (p : Pattern) (ha : d190404 p = 1) (hb : d190580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190399 q = 1) (hb : d190575 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d190399, d190575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44028 q ha hb
    | true =>
      simp only [d190399, d190575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d190400 q = 1) (hb : d190576 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d190400, d190576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190400, d190576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d190401 q = 1) (hb : d190577 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d190401, d190577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d190401, d190577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d190402 q = 1) (hb : d190578 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d190402, d190578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190402, d190578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d190403 q = 1) (hb : d190579 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d190403, d190579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d190403, d190579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d190404 q = 1) (hb : d190580 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d190404, d190580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d190404, d190580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44030 (p : Pattern) (ha : d190410 p = 1) (hb : d190586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190405 q = 1) (hb : d190581 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d190405, d190581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44029 q ha hb
    | true =>
      simp only [d190405, d190581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d190406 q = 1) (hb : d190582 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d190406, d190582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190406, d190582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d190407 q = 1) (hb : d190583 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d190407, d190583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d190407, d190583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d190408 q = 1) (hb : d190584 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d190408, d190584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190408, d190584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d190409 q = 1) (hb : d190585 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d190409, d190585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d190409, d190585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d190410 q = 1) (hb : d190586 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d190410, d190586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d190410, d190586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44031 (p : Pattern) (ha : d190416 p = 1) (hb : d190592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190411 q = 1) (hb : d190587 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d190411, d190587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44030 q ha hb
    | true =>
      simp only [d190411, d190587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d190412 q = 1) (hb : d190588 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d190412, d190588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190412, d190588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d190413 q = 1) (hb : d190589 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d190413, d190589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d190413, d190589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d190414 q = 1) (hb : d190590 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d190414, d190590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d190414, d190590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d190415 q = 1) (hb : d190591 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d190415, d190591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d190415, d190591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d190416 q = 1) (hb : d190592 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d190416, d190592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d190416, d190592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44032 (p : Pattern) (ha : d130386 p = 1) (hb : d190593 p = 1) : d130386 p = 1 := by
  have h0 (q : Pattern) (ha : d130386 q = 1) (hb : d190593 q = 1) : d130386 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro44033 (p : Pattern) (ha : d9296 p = 1) (hb : d51923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9292 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9292, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9292, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9293 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9293, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9293, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9294 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9294, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9294, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9295 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9295, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9295, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d9296 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9296, d51923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9296, d51923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro44034 (p : Pattern) (ha : d19742 p = 1) (hb : d130483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9297 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44033 q ha hb
    | true =>
      simp only [d9297, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19738 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19738, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19738, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19739 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19739, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19739, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19740 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19740, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19740, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19741 q = 1) (hb : d51928 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19741, d51928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19741, d51928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9297 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
    | true =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9298 q = 1) (hb : d100949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9299 q = 1) (hb : d100950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9300 q = 1) (hb : d100951 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9301 q = 1) (hb : d100952 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9301, d100952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9301, d100952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d19742 q = 1) (hb : d130483 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19742, d130483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19742, d130483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro44035 (p : Pattern) (ha : d19748 p = 1) (hb : d130489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19743 q = 1) (hb : d130484 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19743, d130484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44034 q ha hb
    | true =>
      simp only [d19743, d130484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19744 q = 1) (hb : d130485 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19744, d130485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19744, d130485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19745 q = 1) (hb : d130486 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19745, d130486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19745, d130486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19746 q = 1) (hb : d130487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19746, d130487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19746, d130487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19747 q = 1) (hb : d130488 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19747, d130488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19747, d130488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19748 q = 1) (hb : d130489 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19748, d130489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19748, d130489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44036 (p : Pattern) (ha : d19754 p = 1) (hb : d130495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19749 q = 1) (hb : d130490 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19749, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44035 q ha hb
    | true =>
      simp only [d19749, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19750 q = 1) (hb : d130491 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19750, d130491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19750, d130491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19751 q = 1) (hb : d130492 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19751, d130492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19751, d130492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19752 q = 1) (hb : d130493 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19752, d130493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19752, d130493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19753 q = 1) (hb : d130494 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19753, d130494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19753, d130494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19754 q = 1) (hb : d130495 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19754, d130495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19754, d130495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44037 (p : Pattern) (ha : d19760 p = 1) (hb : d130501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19755 q = 1) (hb : d130496 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19755, d130496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19755, d130496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44036 q ha hb
  have h2 (q : Pattern) (ha : d19756 q = 1) (hb : d130497 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d19756, d130497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19756, d130497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19757 q = 1) (hb : d130498 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d19757, d130498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19757, d130498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19758 q = 1) (hb : d130499 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d19758, d130499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19758, d130499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19759 q = 1) (hb : d130500 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d19759, d130500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19759, d130500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19760 q = 1) (hb : d130501 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d19760, d130501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19760, d130501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44038 (p : Pattern) (ha : d9329 p = 1) (hb : d52049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9325 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9325, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9325, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9326 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9326, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9326, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9327 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9327, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9327, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d9292 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9292, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9292, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d9293 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9293, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9293, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9294 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9294, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9294, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d9328 q = 1) (hb : d52048 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9328, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9328, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9295 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9295, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9295, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d9329 q = 1) (hb : d52049 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9329, d52049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9329, d52049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro44039 (p : Pattern) (ha : d19769 p = 1) (hb : d130506 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9330 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44038 q ha hb
    | true =>
      simp only [d9330, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44033 q ha hb
  have h2 (q : Pattern) (ha : d19765 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19765, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19766 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9297 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44033 q ha hb
    | true =>
      simp only [d9297, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19738 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19738, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19738, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19739 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19739, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19739, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19767 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19767, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19767, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19740 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19740, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19740, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19768 q = 1) (hb : d52054 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19768, d52054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19768, d52054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h11 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9297 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
    | true =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9298 q = 1) (hb : d100949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9299 q = 1) (hb : d100950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9333 q = 1) (hb : d100984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9300 q = 1) (hb : d100951 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9334 q = 1) (hb : d100985 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9334, d100985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9334, d100985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19769 q = 1) (hb : d130506 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19769, d130506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19769, d130506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro44040 (p : Pattern) (ha : d19775 p = 1) (hb : d130512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19770 q = 1) (hb : d130507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19770, d130507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44039 q ha hb
    | true =>
      simp only [d19770, d130507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19771 q = 1) (hb : d130508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19771, d130508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19771, d130508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19743 q = 1) (hb : d130484 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19743, d130484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44034 q ha hb
    | true =>
      simp only [d19743, d130484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19744 q = 1) (hb : d130485 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19744, d130485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19744, d130485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19772 q = 1) (hb : d130509 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19772, d130509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19772, d130509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19773 q = 1) (hb : d130510 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19773, d130510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19773, d130510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19774 q = 1) (hb : d130511 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19774, d130511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19774, d130511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19775 q = 1) (hb : d130512 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19775, d130512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19775, d130512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44041 (p : Pattern) (ha : d130215 p = 1) (hb : d130518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19776 q = 1) (hb : d130513 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19776, d130513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44040 q ha hb
    | true =>
      simp only [d19776, d130513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44035 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130490 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130211 q = 1) (hb : d130514 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130211, d130514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130211, d130514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19749 q = 1) (hb : d130490 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19749, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44035 q ha hb
    | true =>
      simp only [d19749, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19750 q = 1) (hb : d130491 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19750, d130491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19750, d130491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130212 q = 1) (hb : d130515 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130212, d130515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130212, d130515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130213 q = 1) (hb : d130516 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130213, d130516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130213, d130516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130214 q = 1) (hb : d130517 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130214, d130517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130214, d130517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130215 q = 1) (hb : d130518 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130215, d130518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130215, d130518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro44042 (p : Pattern) (ha : d130221 p = 1) (hb : d130524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130216 q = 1) (hb : d130519 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130216, d130519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130216, d130519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44041 q ha hb
  have h2 (q : Pattern) (ha : d130217 q = 1) (hb : d130520 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130217, d130520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130217, d130520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d130218 q = 1) (hb : d130521 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130218, d130521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130218, d130521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d130219 q = 1) (hb : d130522 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130219, d130522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130219, d130522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130220 q = 1) (hb : d130523 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130220, d130523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130220, d130523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130221 q = 1) (hb : d130524 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130221, d130524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130221, d130524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44043 (p : Pattern) (ha : d19845 p = 1) (hb : d130554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19749 q = 1) (hb : d130490 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19749, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44035 q ha hb
    | true =>
      simp only [d19749, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19841 q = 1) (hb : d130550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19841, d130550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19841, d130550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19842 q = 1) (hb : d130551 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19842, d130551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19842, d130551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19843 q = 1) (hb : d130552 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19843, d130552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19843, d130552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19844 q = 1) (hb : d130553 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19844, d130553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19844, d130553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19845 q = 1) (hb : d130554 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19845, d130554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19845, d130554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44044 (p : Pattern) (ha : d9388 p = 1) (hb : d126912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9377 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9377, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9377, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9378 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9378, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9378, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9379 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9379, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9379, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d9325 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9325, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9325, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d9326 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9326, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9326, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9327 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9327, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9327, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d9380 q = 1) (hb : d52182 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9380, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9380, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113007 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d9382 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d9383 q = 1) (hb : d113008 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9383, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9383, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9384 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d9385 q = 1) (hb : d113009 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9385, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9385, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9386 q = 1) (hb : d113010 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9386, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9386, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d9292 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9292, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9292, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d9293 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9293, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9293, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d9294 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9294, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d9294, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h26 (q : Pattern) (ha : d9387 q = 1) (hb : d113011 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9387, d113011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9387, d113011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d9388 q = 1) (hb : d126912 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9388, d126912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9388, d126912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro44045 (p : Pattern) (ha : d19809 p = 1) (hb : d130530 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9389 q = 1) (hb : d126913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44044 q ha hb
    | true =>
      simp only [d9389, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44038 q ha hb
  have h2 (q : Pattern) (ha : d19805 q = 1) (hb : d126914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19805, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19805, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19806 q = 1) (hb : d126915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19806, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19806, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9330 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44038 q ha hb
    | true =>
      simp only [d9330, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44033 q ha hb
  have h5 (q : Pattern) (ha : d19765 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19765, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19766 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19807 q = 1) (hb : d126916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19807, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19807, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9297 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44033 q ha hb
    | true =>
      simp only [d9297, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19738 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19738, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19738, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19739 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19739, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19739, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19767 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19767, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19767, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19808 q = 1) (hb : d126917 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19808, d126917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19808, d126917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9389 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
  have h14 (q : Pattern) (ha : d9390 q = 1) (hb : d101023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9391 q = 1) (hb : d101024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h17 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9392 q = 1) (hb : d101025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9297 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
    | true =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d9298 q = 1) (hb : d100949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d9299 q = 1) (hb : d100950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9333 q = 1) (hb : d100984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d9393 q = 1) (hb : d101026 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9393, d101026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9393, d101026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d19809 q = 1) (hb : d130530 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19809, d130530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19809, d130530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro44046 (p : Pattern) (ha : d19815 p = 1) (hb : d130536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19810 q = 1) (hb : d130531 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19810, d130531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44045 q ha hb
    | true =>
      simp only [d19810, d130531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19811 q = 1) (hb : d130532 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19811, d130532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19811, d130532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19770 q = 1) (hb : d130507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19770, d130507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44039 q ha hb
    | true =>
      simp only [d19770, d130507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19771 q = 1) (hb : d130508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19771, d130508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19771, d130508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19812 q = 1) (hb : d130533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19812, d130533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19812, d130533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19813 q = 1) (hb : d130534 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19813, d130534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19813, d130534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19814 q = 1) (hb : d130535 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19814, d130535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19814, d130535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19815 q = 1) (hb : d130536 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19815, d130536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19815, d130536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44047 (p : Pattern) (ha : d19833 p = 1) (hb : d130542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19770 q = 1) (hb : d130507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19770, d130507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44039 q ha hb
    | true =>
      simp only [d19770, d130507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19771 q = 1) (hb : d130508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19771, d130508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19771, d130508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19830 q = 1) (hb : d130539 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19830, d130539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19830, d130539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19831 q = 1) (hb : d130540 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19831, d130540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19831, d130540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19832 q = 1) (hb : d130541 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19832, d130541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19832, d130541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19833 q = 1) (hb : d130542 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19833, d130542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19833, d130542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44048 (p : Pattern) (ha : d130231 p = 1) (hb : d130548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19816 q = 1) (hb : d130537 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19816, d130537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44046 q ha hb
    | true =>
      simp only [d19816, d130537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44040 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130513 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130227 q = 1) (hb : d130538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130227, d130538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130227, d130538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19834 q = 1) (hb : d130543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19834, d130543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44047 q ha hb
    | true =>
      simp only [d19834, d130543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19835 q = 1) (hb : d130544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19835, d130544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19835, d130544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130228 q = 1) (hb : d130545 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130228, d130545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130228, d130545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130229 q = 1) (hb : d130546 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130229, d130546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130229, d130546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130230 q = 1) (hb : d130547 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130230, d130547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130230, d130547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130231 q = 1) (hb : d130548 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130231, d130548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130231, d130548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro44049 (p : Pattern) (ha : d130237 p = 1) (hb : d130560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130232 q = 1) (hb : d130549 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130232, d130549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130232, d130549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44048 q ha hb
  have h2 (q : Pattern) (ha : d19846 q = 1) (hb : d130555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19846, d130555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19846, d130555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44043 q ha hb
  have h3 (q : Pattern) (ha : d130233 q = 1) (hb : d130556 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130233, d130556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130233, d130556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130234 q = 1) (hb : d130557 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130234, d130557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130234, d130557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130235 q = 1) (hb : d130558 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130235, d130558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130235, d130558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130236 q = 1) (hb : d130559 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130236, d130559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130236, d130559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130237 q = 1) (hb : d130560 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130237, d130560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130237, d130560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44050 (p : Pattern) (ha : d130243 p = 1) (hb : d130566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19761 q = 1) (hb : d130502 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d19761, d130502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19761, d130502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44037 q ha hb
  have h2 (q : Pattern) (ha : d19762 q = 1) (hb : d130503 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d19762, d130503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19762, d130503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19763 q = 1) (hb : d130504 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d19763, d130504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19763, d130504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19764 q = 1) (hb : d130505 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d19764, d130505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19764, d130505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130222 q = 1) (hb : d130525 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130222, d130525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130222, d130525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44042 q ha hb
  have h6 (q : Pattern) (ha : d130223 q = 1) (hb : d130526 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130223, d130526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130223, d130526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130224 q = 1) (hb : d130527 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130224, d130527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130224, d130527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130225 q = 1) (hb : d130528 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130225, d130528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130225, d130528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130226 q = 1) (hb : d130529 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130226, d130529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130226, d130529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130238 q = 1) (hb : d130561 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130238, d130561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130238, d130561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44049 q ha hb
  have h11 (q : Pattern) (ha : d130239 q = 1) (hb : d130562 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130239, d130562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130239, d130562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d130240 q = 1) (hb : d130563 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130240, d130563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130240, d130563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d130241 q = 1) (hb : d130564 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130241, d130564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130241, d130564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d130242 q = 1) (hb : d130565 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130242, d130565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130242, d130565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d130243 q = 1) (hb : d130566 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130243, d130566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d130243, d130566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro44051 (p : Pattern) (ha : d19877 p = 1) (hb : d130577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9330 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44038 q ha hb
    | true =>
      simp only [d9330, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44033 q ha hb
  have h2 (q : Pattern) (ha : d19765 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19765, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19766 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19867 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19867, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19867, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19876 q = 1) (hb : d52386 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19876, d52386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19876, d52386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h7 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9487 q = 1) (hb : d101102 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9496 q = 1) (hb : d101111 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9496, d101111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9496, d101111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d19877 q = 1) (hb : d130577 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19877, d130577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19877, d130577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro44052 (p : Pattern) (ha : d19921 p = 1) (hb : d130588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19878 q = 1) (hb : d130578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19878, d130578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44051 q ha hb
    | true =>
      simp only [d19878, d130578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19879 q = 1) (hb : d130579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19879, d130579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19879, d130579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19918 q = 1) (hb : d130585 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19918, d130585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19918, d130585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19919 q = 1) (hb : d130586 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19919, d130586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19919, d130586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19920 q = 1) (hb : d130587 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19920, d130587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19920, d130587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19921 q = 1) (hb : d130588 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19921, d130588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19921, d130588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44053 (p : Pattern) (ha : d19927 p = 1) (hb : d130607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19922 q = 1) (hb : d130602 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19922, d130602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44052 q ha hb
    | true =>
      simp only [d19922, d130602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19923 q = 1) (hb : d130603 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19923, d130603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19923, d130603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19924 q = 1) (hb : d130604 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19924, d130604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19924, d130604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19925 q = 1) (hb : d130605 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19925, d130605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19925, d130605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19926 q = 1) (hb : d130606 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19926, d130606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19926, d130606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19927 q = 1) (hb : d130607 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19927, d130607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19927, d130607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44054 (p : Pattern) (ha : d9474 p = 1) (hb : d127053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52363 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9449 q = 1) (hb : d52364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9449, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9449, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9450 q = 1) (hb : d52365 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9450, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9450, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9451 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9451, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9451, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d127047 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9458 q = 1) (hb : d101073 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23272 q ha hb
    | true =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d9459 q = 1) (hb : d127048 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9459, d127048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9459, d127048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9460 q = 1) (hb : d101075 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d9461 q = 1) (hb : d127049 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9461, d127049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9461, d127049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9462 q = 1) (hb : d127050 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9462, d127050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9462, d127050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d9463 q = 1) (hb : d127051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9463, d127051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9463, d127051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d9468 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d9469 q = 1) (hb : d113215 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9469, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9469, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9470 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d9471 q = 1) (hb : d113216 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9471, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9471, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9472 q = 1) (hb : d113217 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9472, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9472, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d113007 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d9382 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d9383 q = 1) (hb : d113008 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9383, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9383, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9384 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d9385 q = 1) (hb : d113009 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9385, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9385, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d9386 q = 1) (hb : d113010 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9386, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d9386, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h26 (q : Pattern) (ha : d9473 q = 1) (hb : d127052 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9473, d127052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9473, d127052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d9474 q = 1) (hb : d127053 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9474, d127053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9474, d127053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro44055 (p : Pattern) (ha : d9478 p = 1) (hb : d127057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113007 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9382 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9383 q = 1) (hb : d113008 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9383, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9383, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9384 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9385 q = 1) (hb : d113009 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9385, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9385, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9386 q = 1) (hb : d113010 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9386, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9386, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d9292 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9292, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9292, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d9293 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9293, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9293, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9294 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9294, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9294, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d9387 q = 1) (hb : d113011 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9387, d113011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9387, d113011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9295 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9295, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9295, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d9478 q = 1) (hb : d127057 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9478, d127057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9478, d127057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro44056 (p : Pattern) (ha : d19864 p = 1) (hb : d130567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9475 q = 1) (hb : d127054 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9475, d127054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44054 q ha hb
    | true =>
      simp only [d9475, d127054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44044 q ha hb
  have h2 (q : Pattern) (ha : d19858 q = 1) (hb : d127055 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19858, d127055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19858, d127055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19859 q = 1) (hb : d127056 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19859, d127056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19859, d127056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9479 q = 1) (hb : d127058 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9479, d127058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44044 q ha hb
    | true =>
      simp only [d9479, d127058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44055 q ha hb
  have h5 (q : Pattern) (ha : d19860 q = 1) (hb : d127059 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19860, d127059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19860, d127059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19861 q = 1) (hb : d127060 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19861, d127060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19861, d127060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19862 q = 1) (hb : d127061 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19862, d127061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19862, d127061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9389 q = 1) (hb : d126913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44044 q ha hb
    | true =>
      simp only [d9389, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44038 q ha hb
  have h9 (q : Pattern) (ha : d19805 q = 1) (hb : d126914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19805, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19805, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19806 q = 1) (hb : d126915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19806, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19806, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9330 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44038 q ha hb
    | true =>
      simp only [d9330, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44033 q ha hb
  have h12 (q : Pattern) (ha : d19765 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19765, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19766 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19807 q = 1) (hb : d126916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19807, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19807, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19863 q = 1) (hb : d127062 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19863, d127062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19863, d127062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9475 q = 1) (hb : d101090 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9475, d101090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23274 q ha hb
    | true =>
      simp only [d9475, d101090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
  have h17 (q : Pattern) (ha : d9476 q = 1) (hb : d101091 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9476, d101091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9476, d101091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9477 q = 1) (hb : d101092 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9477, d101092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9477, d101092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9479 q = 1) (hb : d101094 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9479, d101094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9479, d101094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23275 q ha hb
  have h20 (q : Pattern) (ha : d9480 q = 1) (hb : d101095 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9480, d101095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9480, d101095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d9481 q = 1) (hb : d101096 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9481, d101096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9481, d101096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d9482 q = 1) (hb : d101097 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9482, d101097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9482, d101097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9389 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
  have h24 (q : Pattern) (ha : d9390 q = 1) (hb : d101023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d9391 q = 1) (hb : d101024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h27 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d9392 q = 1) (hb : d101025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d9483 q = 1) (hb : d101098 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9483, d101098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9483, d101098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d19864 q = 1) (hb : d130567 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19864, d130567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19864, d130567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro44057 (p : Pattern) (ha : d19869 p = 1) (hb : d130570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9389 q = 1) (hb : d126913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44044 q ha hb
    | true =>
      simp only [d9389, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44038 q ha hb
  have h2 (q : Pattern) (ha : d19805 q = 1) (hb : d126914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19805, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19805, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19806 q = 1) (hb : d126915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19806, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19806, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9330 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44038 q ha hb
    | true =>
      simp only [d9330, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44033 q ha hb
  have h5 (q : Pattern) (ha : d19765 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19765, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19766 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19807 q = 1) (hb : d126916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19807, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19807, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19867 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19867, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19867, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19868 q = 1) (hb : d127066 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19868, d127066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19868, d127066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9389 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
  have h11 (q : Pattern) (ha : d9390 q = 1) (hb : d101023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9391 q = 1) (hb : d101024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h14 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9392 q = 1) (hb : d101025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9487 q = 1) (hb : d101102 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9488 q = 1) (hb : d101103 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9488, d101103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9488, d101103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19869 q = 1) (hb : d130570 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19869, d130570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19869, d130570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro44058 (p : Pattern) (ha : d19875 p = 1) (hb : d130576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19865 q = 1) (hb : d130568 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19865, d130568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44056 q ha hb
    | true =>
      simp only [d19865, d130568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19866 q = 1) (hb : d130569 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19866, d130569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19866, d130569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19870 q = 1) (hb : d130571 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19870, d130571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44057 q ha hb
    | true =>
      simp only [d19870, d130571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19871 q = 1) (hb : d130572 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19871, d130572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19871, d130572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19872 q = 1) (hb : d130573 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19872, d130573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19872, d130573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19873 q = 1) (hb : d130574 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19873, d130574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19873, d130574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19874 q = 1) (hb : d130575 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19874, d130575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19874, d130575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19875 q = 1) (hb : d130576 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19875, d130576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19875, d130576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44059 (p : Pattern) (ha : d19883 p = 1) (hb : d130583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19870 q = 1) (hb : d130571 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19870, d130571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44057 q ha hb
    | true =>
      simp only [d19870, d130571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19871 q = 1) (hb : d130572 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19871, d130572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19871, d130572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19878 q = 1) (hb : d130578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19878, d130578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44051 q ha hb
    | true =>
      simp only [d19878, d130578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19879 q = 1) (hb : d130579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19879, d130579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19879, d130579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19880 q = 1) (hb : d130580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19880, d130580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19880, d130580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19881 q = 1) (hb : d130581 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19881, d130581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19881, d130581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19882 q = 1) (hb : d130582 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19882, d130582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19882, d130582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19883 q = 1) (hb : d130583 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19883, d130583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19883, d130583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44060 (p : Pattern) (ha : d19910 p = 1) (hb : d130594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19870 q = 1) (hb : d130571 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19870, d130571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44057 q ha hb
    | true =>
      simp only [d19870, d130571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19871 q = 1) (hb : d130572 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19871, d130572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19871, d130572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19907 q = 1) (hb : d130591 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19907, d130591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19907, d130591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19908 q = 1) (hb : d130592 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19908, d130592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19908, d130592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19909 q = 1) (hb : d130593 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19909, d130593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19909, d130593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19910 q = 1) (hb : d130594 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19910, d130594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19910, d130594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44061 (p : Pattern) (ha : d130248 p = 1) (hb : d130600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19884 q = 1) (hb : d130584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19884, d130584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44058 q ha hb
    | true =>
      simp only [d19884, d130584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44059 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130589 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130244 q = 1) (hb : d130590 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130244, d130590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130244, d130590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19911 q = 1) (hb : d130595 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19911, d130595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44060 q ha hb
    | true =>
      simp only [d19911, d130595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19912 q = 1) (hb : d130596 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19912, d130596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19912, d130596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130245 q = 1) (hb : d130597 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130245, d130597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130245, d130597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130246 q = 1) (hb : d130598 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130246, d130598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130246, d130598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130247 q = 1) (hb : d130599 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130247, d130599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130247, d130599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130248 q = 1) (hb : d130600 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130248, d130600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130248, d130600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro44062 (p : Pattern) (ha : d130254 p = 1) (hb : d130613 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130249 q = 1) (hb : d130601 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130249, d130601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130249, d130601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44061 q ha hb
  have h2 (q : Pattern) (ha : d19928 q = 1) (hb : d130608 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19928, d130608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19928, d130608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44053 q ha hb
  have h3 (q : Pattern) (ha : d130250 q = 1) (hb : d130609 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130250, d130609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130250, d130609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130251 q = 1) (hb : d130610 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130251, d130610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130251, d130610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130252 q = 1) (hb : d130611 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130252, d130611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130252, d130611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130253 q = 1) (hb : d130612 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130253, d130612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130253, d130612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130254 q = 1) (hb : d130613 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130254, d130613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130254, d130613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44063 (p : Pattern) (ha : d130260 p = 1) (hb : d130619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130255 q = 1) (hb : d130614 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130255, d130614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130255, d130614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44062 q ha hb
  have h2 (q : Pattern) (ha : d130256 q = 1) (hb : d130615 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130256, d130615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130256, d130615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130257 q = 1) (hb : d130616 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130257, d130616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130257, d130616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130258 q = 1) (hb : d130617 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130258, d130617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130258, d130617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130259 q = 1) (hb : d130618 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130259, d130618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130259, d130618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130260 q = 1) (hb : d130619 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130260, d130619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130260, d130619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44064 (p : Pattern) (ha : d9619 p = 1) (hb : d52600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9377 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9377, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9377, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9378 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9378, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9378, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9379 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9379, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9379, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d9604 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9604, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9604, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d9605 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9605, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9605, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9606 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9606, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9606, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d9618 q = 1) (hb : d52594 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9618, d52594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9618, d52594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9612 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9612, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9612, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d9619 q = 1) (hb : d52600 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9619, d52600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9619, d52600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro44065 (p : Pattern) (ha : d9623 p = 1) (hb : d52605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9604 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9604, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9604, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9605 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9605, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9605, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9606 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9606, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9606, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9612 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9612, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9612, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d9623 q = 1) (hb : d52605 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9623, d52605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9623, d52605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro44066 (p : Pattern) (ha : d19965 p = 1) (hb : d130631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9624 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44064 q ha hb
    | true =>
      simp only [d9624, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44065 q ha hb
  have h2 (q : Pattern) (ha : d19948 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19948, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19948, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19949 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19949, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19949, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19955 q = 1) (hb : d52614 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19955, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19955, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19964 q = 1) (hb : d52623 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19964, d52623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19964, d52623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9624 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23285 q ha hb
  have h7 (q : Pattern) (ha : d9625 q = 1) (hb : d101205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9626 q = 1) (hb : d101206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9632 q = 1) (hb : d101212 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9641 q = 1) (hb : d101221 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9641, d101221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9641, d101221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d19965 q = 1) (hb : d130631 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19965, d130631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19965, d130631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro44067 (p : Pattern) (ha : d20011 p = 1) (hb : d130642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19966 q = 1) (hb : d130632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19966, d130632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44066 q ha hb
    | true =>
      simp only [d19966, d130632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19967 q = 1) (hb : d130633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19967, d130633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19967, d130633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20008 q = 1) (hb : d130639 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20008, d130639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20008, d130639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20009 q = 1) (hb : d130640 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20009, d130640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20009, d130640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20010 q = 1) (hb : d130641 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20010, d130641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20010, d130641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20011 q = 1) (hb : d130642 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20011, d130642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20011, d130642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44068 (p : Pattern) (ha : d20017 p = 1) (hb : d130661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20012 q = 1) (hb : d130656 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20012, d130656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44067 q ha hb
    | true =>
      simp only [d20012, d130656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20013 q = 1) (hb : d130657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20013, d130657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20013, d130657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20014 q = 1) (hb : d130658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20014, d130658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20014, d130658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20015 q = 1) (hb : d130659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20015, d130659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20015, d130659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20016 q = 1) (hb : d130660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20016, d130660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20016, d130660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20017 q = 1) (hb : d130661 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20017, d130661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20017, d130661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44069 (p : Pattern) (ha : d9603 p = 1) (hb : d127219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52584 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d834 q = 1) (hb : d52511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro122 q ha hb
    | true =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9576 q = 1) (hb : d52585 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9576, d52585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9576, d52585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d835 q = 1) (hb : d52512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9577 q = 1) (hb : d52586 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9577, d52586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9577, d52586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9578 q = 1) (hb : d52587 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9578, d52587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9578, d52587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d127213 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9587 q = 1) (hb : d101167 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d101167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23290 q ha hb
    | true =>
      simp only [d9587, d101167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d9588 q = 1) (hb : d127214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9588, d127214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9588, d127214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9589 q = 1) (hb : d101169 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9589, d101169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9589, d101169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d9590 q = 1) (hb : d127215 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9590, d127215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9590, d127215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9591 q = 1) (hb : d127216 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9591, d127216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9591, d127216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d9592 q = 1) (hb : d127217 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9592, d127217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9592, d127217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d122847 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d9597 q = 1) (hb : d101177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23291 q ha hb
    | true =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d9598 q = 1) (hb : d122848 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9598, d122848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9598, d122848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9599 q = 1) (hb : d101179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9599, d101179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9599, d101179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d9600 q = 1) (hb : d122849 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9600, d122849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9600, d122849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9601 q = 1) (hb : d122850 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9601, d122850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9601, d122850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d9468 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d9469 q = 1) (hb : d113215 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9469, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9469, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9470 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d9471 q = 1) (hb : d113216 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9471, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9471, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d9472 q = 1) (hb : d113217 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9472, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d9472, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h26 (q : Pattern) (ha : d9602 q = 1) (hb : d127218 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9602, d127218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9602, d127218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d9603 q = 1) (hb : d127219 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9603, d127219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9603, d127219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro44070 (p : Pattern) (ha : d9608 p = 1) (hb : d127220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52363 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9449 q = 1) (hb : d52364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9449, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9449, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9450 q = 1) (hb : d52365 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9450, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9450, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9451 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9451, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9451, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d127047 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9458 q = 1) (hb : d101073 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23272 q ha hb
    | true =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d9459 q = 1) (hb : d127048 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9459, d127048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9459, d127048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9460 q = 1) (hb : d101075 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9460, d101075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d9461 q = 1) (hb : d127049 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9461, d127049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9461, d127049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9462 q = 1) (hb : d127050 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9462, d127050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9462, d127050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d9463 q = 1) (hb : d127051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9463, d127051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9463, d127051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d9468 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d9469 q = 1) (hb : d113215 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9469, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9469, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9470 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d9471 q = 1) (hb : d113216 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9471, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9471, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9472 q = 1) (hb : d113217 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9472, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9472, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d9604 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9604, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9604, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d9605 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9605, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9605, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d9606 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9606, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d9606, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h26 (q : Pattern) (ha : d9607 q = 1) (hb : d113218 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9607, d113218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9607, d113218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d9608 q = 1) (hb : d127220 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9608, d127220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9608, d127220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro44071 (p : Pattern) (ha : d9613 p = 1) (hb : d127224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9468 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9469 q = 1) (hb : d113215 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9469, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9469, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9470 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9471 q = 1) (hb : d113216 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9471, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9471, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9472 q = 1) (hb : d113217 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9472, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9472, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d9604 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9604, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9604, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d9605 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9605, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9605, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9606 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9606, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9606, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d9607 q = 1) (hb : d113218 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9607, d113218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9607, d113218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9612 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9612, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9612, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d9613 q = 1) (hb : d127224 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9613, d127224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9613, d127224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro44072 (p : Pattern) (ha : d19952 p = 1) (hb : d130621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9609 q = 1) (hb : d127221 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9609, d127221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44069 q ha hb
    | true =>
      simp only [d9609, d127221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44070 q ha hb
  have h2 (q : Pattern) (ha : d19941 q = 1) (hb : d127222 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19941, d127222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19941, d127222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19942 q = 1) (hb : d127223 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19942, d127223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19942, d127223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9614 q = 1) (hb : d127225 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9614, d127225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44070 q ha hb
    | true =>
      simp only [d9614, d127225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44071 q ha hb
  have h5 (q : Pattern) (ha : d19943 q = 1) (hb : d127226 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19943, d127226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19943, d127226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19944 q = 1) (hb : d127227 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19944, d127227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19944, d127227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19945 q = 1) (hb : d127228 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19945, d127228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19945, d127228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9620 q = 1) (hb : d127229 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d127229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44070 q ha hb
    | true =>
      simp only [d9620, d127229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44064 q ha hb
  have h9 (q : Pattern) (ha : d19946 q = 1) (hb : d127230 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19946, d127230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19946, d127230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19947 q = 1) (hb : d127231 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19947, d127231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19947, d127231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9624 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44064 q ha hb
    | true =>
      simp only [d9624, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44065 q ha hb
  have h12 (q : Pattern) (ha : d19948 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19948, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19948, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19949 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19949, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19949, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19950 q = 1) (hb : d127232 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19950, d127232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19950, d127232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19951 q = 1) (hb : d127233 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19951, d127233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19951, d127233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9609 q = 1) (hb : d101189 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9609, d101189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23292 q ha hb
    | true =>
      simp only [d9609, d101189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
  have h17 (q : Pattern) (ha : d9610 q = 1) (hb : d101190 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9610, d101190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9610, d101190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9611 q = 1) (hb : d101191 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9611, d101191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9611, d101191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9614 q = 1) (hb : d101194 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9614, d101194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
    | true =>
      simp only [d9614, d101194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23294 q ha hb
  have h20 (q : Pattern) (ha : d9615 q = 1) (hb : d101195 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9615, d101195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9615, d101195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d9616 q = 1) (hb : d101196 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9616, d101196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9616, d101196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d9617 q = 1) (hb : d101197 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9617, d101197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9617, d101197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9620 q = 1) (hb : d101200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
    | true =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
  have h24 (q : Pattern) (ha : d9621 q = 1) (hb : d101201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d9622 q = 1) (hb : d101202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d9624 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23285 q ha hb
  have h27 (q : Pattern) (ha : d9625 q = 1) (hb : d101205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d9626 q = 1) (hb : d101206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d9627 q = 1) (hb : d101207 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d9628 q = 1) (hb : d101208 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9628, d101208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9628, d101208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d19952 q = 1) (hb : d130621 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19952, d130621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19952, d130621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro44073 (p : Pattern) (ha : d19957 p = 1) (hb : d130624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9620 q = 1) (hb : d127229 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d127229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44070 q ha hb
    | true =>
      simp only [d9620, d127229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44064 q ha hb
  have h2 (q : Pattern) (ha : d19946 q = 1) (hb : d127230 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19946, d127230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19946, d127230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19947 q = 1) (hb : d127231 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19947, d127231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19947, d127231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9624 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44064 q ha hb
    | true =>
      simp only [d9624, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44065 q ha hb
  have h5 (q : Pattern) (ha : d19948 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19948, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19948, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19949 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19949, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19949, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19950 q = 1) (hb : d127232 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19950, d127232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19950, d127232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19955 q = 1) (hb : d52614 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19955, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19955, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19956 q = 1) (hb : d127237 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19956, d127237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19956, d127237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9620 q = 1) (hb : d101200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
    | true =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
  have h11 (q : Pattern) (ha : d9621 q = 1) (hb : d101201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9622 q = 1) (hb : d101202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9624 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23285 q ha hb
  have h14 (q : Pattern) (ha : d9625 q = 1) (hb : d101205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9626 q = 1) (hb : d101206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9627 q = 1) (hb : d101207 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9632 q = 1) (hb : d101212 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9633 q = 1) (hb : d101213 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9633, d101213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9633, d101213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19957 q = 1) (hb : d130624 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19957, d130624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19957, d130624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro44074 (p : Pattern) (ha : d19963 p = 1) (hb : d130630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19953 q = 1) (hb : d130622 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19953, d130622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44072 q ha hb
    | true =>
      simp only [d19953, d130622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19954 q = 1) (hb : d130623 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19954, d130623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19954, d130623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19958 q = 1) (hb : d130625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19958, d130625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44073 q ha hb
    | true =>
      simp only [d19958, d130625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19959 q = 1) (hb : d130626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19959, d130626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19959, d130626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19960 q = 1) (hb : d130627 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19960, d130627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19960, d130627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19961 q = 1) (hb : d130628 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19961, d130628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19961, d130628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19962 q = 1) (hb : d130629 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19962, d130629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19962, d130629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19963 q = 1) (hb : d130630 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19963, d130630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19963, d130630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44075 (p : Pattern) (ha : d19971 p = 1) (hb : d130637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19958 q = 1) (hb : d130625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19958, d130625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44073 q ha hb
    | true =>
      simp only [d19958, d130625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19959 q = 1) (hb : d130626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19959, d130626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19959, d130626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19966 q = 1) (hb : d130632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19966, d130632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44066 q ha hb
    | true =>
      simp only [d19966, d130632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19967 q = 1) (hb : d130633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19967, d130633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19967, d130633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19968 q = 1) (hb : d130634 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19968, d130634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19968, d130634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19969 q = 1) (hb : d130635 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19969, d130635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19969, d130635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19970 q = 1) (hb : d130636 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19970, d130636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19970, d130636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19971 q = 1) (hb : d130637 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19971, d130637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19971, d130637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44076 (p : Pattern) (ha : d20000 p = 1) (hb : d130648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19958 q = 1) (hb : d130625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19958, d130625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44073 q ha hb
    | true =>
      simp only [d19958, d130625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19959 q = 1) (hb : d130626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19959, d130626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19959, d130626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19997 q = 1) (hb : d130645 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19997, d130645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19997, d130645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19998 q = 1) (hb : d130646 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19998, d130646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19998, d130646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19999 q = 1) (hb : d130647 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19999, d130647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19999, d130647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20000 q = 1) (hb : d130648 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20000, d130648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20000, d130648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44077 (p : Pattern) (ha : d130266 p = 1) (hb : d130654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19972 q = 1) (hb : d130638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19972, d130638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44074 q ha hb
    | true =>
      simp only [d19972, d130638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44075 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130643 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130262 q = 1) (hb : d130644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130262, d130644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130262, d130644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20001 q = 1) (hb : d130649 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20001, d130649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44076 q ha hb
    | true =>
      simp only [d20001, d130649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20002 q = 1) (hb : d130650 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20002, d130650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20002, d130650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130263 q = 1) (hb : d130651 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130263, d130651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130263, d130651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130264 q = 1) (hb : d130652 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130264, d130652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130264, d130652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130265 q = 1) (hb : d130653 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130265, d130653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130265, d130653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130266 q = 1) (hb : d130654 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130266, d130654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130266, d130654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro44078 (p : Pattern) (ha : d130272 p = 1) (hb : d130667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130267 q = 1) (hb : d130655 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130267, d130655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130267, d130655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44077 q ha hb
  have h2 (q : Pattern) (ha : d20018 q = 1) (hb : d130662 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20018, d130662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20018, d130662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44068 q ha hb
  have h3 (q : Pattern) (ha : d130268 q = 1) (hb : d130663 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130268, d130663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130268, d130663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130269 q = 1) (hb : d130664 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130269, d130664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130269, d130664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130270 q = 1) (hb : d130665 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130270, d130665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130270, d130665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130271 q = 1) (hb : d130666 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130271, d130666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130271, d130666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130272 q = 1) (hb : d130667 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130272, d130667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130272, d130667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44079 (p : Pattern) (ha : d130278 p = 1) (hb : d130673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130273 q = 1) (hb : d130668 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130273, d130668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130273, d130668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44078 q ha hb
  have h2 (q : Pattern) (ha : d130274 q = 1) (hb : d130669 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130274, d130669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130274, d130669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130275 q = 1) (hb : d130670 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130275, d130670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130275, d130670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130276 q = 1) (hb : d130671 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130276, d130671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130276, d130671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130277 q = 1) (hb : d130672 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130277, d130672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130277, d130672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130278 q = 1) (hb : d130673 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130278, d130673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130278, d130673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44080 (p : Pattern) (ha : d9833 p = 1) (hb : d127473 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9826 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9826, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9826, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9827 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9827, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9827, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9828 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9828, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9828, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d9829 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9829, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9829, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1122 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d9830 q = 1) (hb : d52881 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9830, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9830, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9831 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9831, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9831, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d9832 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9832, d52883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9832, d52883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123129 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d9800 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d9801 q = 1) (hb : d123130 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9801, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9801, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9802 q = 1) (hb : d101323 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d9803 q = 1) (hb : d123131 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9803, d123131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9803, d123131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9804 q = 1) (hb : d123132 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9804, d123132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9804, d123132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d9820 q = 1) (hb : d123133 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9820, d123133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9820, d123133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h21 (q : Pattern) (ha : d9833 q = 1) (hb : d127473 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9833, d127473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9833, d127473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro44081 (p : Pattern) (ha : d9869 p = 1) (hb : d123167 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9829 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9829, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9829, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1122 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9830 q = 1) (hb : d52881 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9830, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9830, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9831 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9831, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9831, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9868 q = 1) (hb : d52888 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9868, d52888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9868, d52888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123144 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9844 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d9845 q = 1) (hb : d123145 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9845, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9845, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9846 q = 1) (hb : d101367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d9847 q = 1) (hb : d123146 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9847, d123146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9847, d123146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9848 q = 1) (hb : d123147 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9848, d123147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9848, d123147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d9849 q = 1) (hb : d123148 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9849, d123148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9849, d123148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d9869 q = 1) (hb : d123167 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9869, d123167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9869, d123167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro44082 (p : Pattern) (ha : d20059 p = 1) (hb : d130686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9870 q = 1) (hb : d127494 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, d127494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44080 q ha hb
    | true =>
      simp only [d9870, d127494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44081 q ha hb
  have h2 (q : Pattern) (ha : d20055 q = 1) (hb : d127495 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20055, d127495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20055, d127495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20056 q = 1) (hb : d127496 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20056, d127496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20056, d127496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20057 q = 1) (hb : d127497 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20057, d127497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20057, d127497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20058 q = 1) (hb : d127498 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20058, d127498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20058, d127498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9870 q = 1) (hb : d101391 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23306 q ha hb
  have h7 (q : Pattern) (ha : d9871 q = 1) (hb : d101392 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9872 q = 1) (hb : d101393 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9873 q = 1) (hb : d101394 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9874 q = 1) (hb : d101395 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9874, d101395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9874, d101395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20059 q = 1) (hb : d130686 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20059, d130686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20059, d130686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro44083 (p : Pattern) (ha : d20114 p = 1) (hb : d130704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20060 q = 1) (hb : d130687 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20060, d130687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44082 q ha hb
    | true =>
      simp only [d20060, d130687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20061 q = 1) (hb : d130688 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20061, d130688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20061, d130688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20111 q = 1) (hb : d130701 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20111, d130701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20111, d130701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20112 q = 1) (hb : d130702 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20112, d130702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20112, d130702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20113 q = 1) (hb : d130703 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20113, d130703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20113, d130703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20114 q = 1) (hb : d130704 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20114, d130704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20114, d130704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44084 (p : Pattern) (ha : d20120 p = 1) (hb : d130726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20115 q = 1) (hb : d130721 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20115, d130721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44083 q ha hb
    | true =>
      simp only [d20115, d130721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20116 q = 1) (hb : d130722 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20116, d130722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20116, d130722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20117 q = 1) (hb : d130723 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20117, d130723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20117, d130723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20118 q = 1) (hb : d130724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20118, d130724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20118, d130724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20119 q = 1) (hb : d130725 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20119, d130725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20119, d130725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20120 q = 1) (hb : d130726 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20120, d130726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20120, d130726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44085 (p : Pattern) (ha : d9784 p = 1) (hb : d127456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1210 q = 1) (hb : d52791 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro174 q ha hb
    | true =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9746 q = 1) (hb : d52865 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9746, d52865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9746, d52865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1211 q = 1) (hb : d52792 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9747 q = 1) (hb : d52866 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9747, d52866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9747, d52866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9748 q = 1) (hb : d52867 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9748, d52867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9748, d52867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d127450 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9753 q = 1) (hb : d101274 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9753, d101274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23310 q ha hb
    | true =>
      simp only [d9753, d101274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d9754 q = 1) (hb : d127451 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9754, d127451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9754, d127451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9755 q = 1) (hb : d101276 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9755, d101276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9755, d101276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d9756 q = 1) (hb : d127452 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9756, d127452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9756, d127452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9757 q = 1) (hb : d127453 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9757, d127453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9757, d127453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d9758 q = 1) (hb : d127454 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9758, d127454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9758, d127454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123112 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d9763 q = 1) (hb : d101284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9763, d101284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23311 q ha hb
    | true =>
      simp only [d9763, d101284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d9764 q = 1) (hb : d123113 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9764, d123113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9764, d123113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9765 q = 1) (hb : d101286 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9765, d101286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9765, d101286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d9766 q = 1) (hb : d123114 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9766, d123114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9766, d123114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9767 q = 1) (hb : d123115 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9767, d123115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9767, d123115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d123119 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d9778 q = 1) (hb : d101299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23313 q ha hb
    | true =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d9779 q = 1) (hb : d123120 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9779, d123120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9779, d123120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9780 q = 1) (hb : d101301 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d9781 q = 1) (hb : d123121 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9781, d123121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9781, d123121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d9782 q = 1) (hb : d123122 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9782, d123122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d9782, d123122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h26 (q : Pattern) (ha : d9783 q = 1) (hb : d127455 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9783, d127455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9783, d127455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d9784 q = 1) (hb : d127456 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9784, d127456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9784, d127456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro44086 (p : Pattern) (ha : d9806 p = 1) (hb : d127463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52868 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1100 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9785 q = 1) (hb : d52869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9785, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9785, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1101 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9786 q = 1) (hb : d52870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9786, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9786, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9787 q = 1) (hb : d52871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9787, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9787, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d127457 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9789 q = 1) (hb : d101310 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, d101310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23315 q ha hb
    | true =>
      simp only [d9789, d101310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d9790 q = 1) (hb : d127458 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9790, d127458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9790, d127458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9791 q = 1) (hb : d101312 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9791, d101312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9791, d101312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d9792 q = 1) (hb : d127459 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9792, d127459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9792, d127459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9793 q = 1) (hb : d127460 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9793, d127460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9793, d127460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d9794 q = 1) (hb : d127461 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9794, d127461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9794, d127461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123119 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d9778 q = 1) (hb : d101299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23313 q ha hb
    | true =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d9779 q = 1) (hb : d123120 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9779, d123120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9779, d123120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9780 q = 1) (hb : d101301 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d9781 q = 1) (hb : d123121 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9781, d123121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9781, d123121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9782 q = 1) (hb : d123122 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9782, d123122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9782, d123122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d123129 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d9800 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d9801 q = 1) (hb : d123130 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9801, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9801, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9802 q = 1) (hb : d101323 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d9803 q = 1) (hb : d123131 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9803, d123131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9803, d123131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d9804 q = 1) (hb : d123132 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9804, d123132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d9804, d123132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h26 (q : Pattern) (ha : d9805 q = 1) (hb : d127462 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9805, d127462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9805, d127462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d9806 q = 1) (hb : d127463 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9806, d127463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9806, d127463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro44087 (p : Pattern) (ha : d9821 p = 1) (hb : d127468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113452 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9814 q = 1) (hb : d101335 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23317 q ha hb
    | true =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9815 q = 1) (hb : d113453 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9815, d113453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9815, d113453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9816 q = 1) (hb : d101337 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9816, d101337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9816, d101337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9817 q = 1) (hb : d113454 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9817, d113454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9817, d113454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9818 q = 1) (hb : d113455 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9818, d113455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9818, d113455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d123129 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9800 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d9801 q = 1) (hb : d123130 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9801, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9801, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9802 q = 1) (hb : d101323 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d9803 q = 1) (hb : d123131 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9803, d123131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9803, d123131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9804 q = 1) (hb : d123132 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9804, d123132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9804, d123132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d9819 q = 1) (hb : d127467 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9819, d127467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9819, d127467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9820 q = 1) (hb : d123133 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9820, d123133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9820, d123133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d9821 q = 1) (hb : d127468 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9821, d127468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9821, d127468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro44088 (p : Pattern) (ha : d9850 p = 1) (hb : d123149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76090 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5018 q = 1) (hb : d69108 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7947 q ha hb
    | true =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9837 q = 1) (hb : d76091 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9837, d76091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9837, d76091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5019 q = 1) (hb : d69109 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, d69109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5019, d69109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9838 q = 1) (hb : d76092 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9838, d76092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9838, d76092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9839 q = 1) (hb : d76093 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9839, d76093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9839, d76093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9840 q = 1) (hb : d76094 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9840, d76094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9840, d76094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123144 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9844 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d9845 q = 1) (hb : d123145 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9845, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9845, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9846 q = 1) (hb : d101367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d9847 q = 1) (hb : d123146 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9847, d123146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9847, d123146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9848 q = 1) (hb : d123147 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9848, d123147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9848, d123147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d9849 q = 1) (hb : d123148 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9849, d123148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9849, d123148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d9850 q = 1) (hb : d123149 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9850, d123149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9850, d123149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro44089 (p : Pattern) (ha : d20043 p = 1) (hb : d130676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9807 q = 1) (hb : d127464 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9807, d127464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44085 q ha hb
    | true =>
      simp only [d9807, d127464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44086 q ha hb
  have h2 (q : Pattern) (ha : d20032 q = 1) (hb : d127465 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20032, d127465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20032, d127465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20033 q = 1) (hb : d127466 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20033, d127466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20033, d127466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9822 q = 1) (hb : d127469 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9822, d127469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44086 q ha hb
    | true =>
      simp only [d9822, d127469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44087 q ha hb
  have h5 (q : Pattern) (ha : d20034 q = 1) (hb : d127470 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20034, d127470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20034, d127470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20035 q = 1) (hb : d127471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20035, d127471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20035, d127471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20036 q = 1) (hb : d127472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20036, d127472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20036, d127472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9834 q = 1) (hb : d127474 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44086 q ha hb
    | true =>
      simp only [d9834, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44080 q ha hb
  have h9 (q : Pattern) (ha : d20037 q = 1) (hb : d127475 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20037, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20037, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20038 q = 1) (hb : d127476 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20038, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20038, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9851 q = 1) (hb : d127477 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44080 q ha hb
    | true =>
      simp only [d9851, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44088 q ha hb
  have h12 (q : Pattern) (ha : d20039 q = 1) (hb : d127478 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20039, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20039, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20040 q = 1) (hb : d127479 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20040, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20040, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d20041 q = 1) (hb : d127480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20041, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20041, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d20042 q = 1) (hb : d127481 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20042, d127481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20042, d127481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9807 q = 1) (hb : d101328 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9807, d101328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23314 q ha hb
    | true =>
      simp only [d9807, d101328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
  have h17 (q : Pattern) (ha : d9808 q = 1) (hb : d101329 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9808, d101329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9808, d101329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9809 q = 1) (hb : d101330 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9809, d101330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9809, d101330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9822 q = 1) (hb : d101343 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9822, d101343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9822, d101343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23318 q ha hb
  have h20 (q : Pattern) (ha : d9823 q = 1) (hb : d101344 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9823, d101344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9823, d101344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d9824 q = 1) (hb : d101345 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9824, d101345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9824, d101345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d9825 q = 1) (hb : d101346 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9825, d101346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9825, d101346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h24 (q : Pattern) (ha : d9835 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d9836 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h27 (q : Pattern) (ha : d9852 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d9853 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d9854 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d9855 q = 1) (hb : d101376 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9855, d101376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9855, d101376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d20043 q = 1) (hb : d130676 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20043, d130676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20043, d130676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro44090 (p : Pattern) (ha : d20048 p = 1) (hb : d130679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9834 q = 1) (hb : d127474 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44086 q ha hb
    | true =>
      simp only [d9834, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44080 q ha hb
  have h2 (q : Pattern) (ha : d20037 q = 1) (hb : d127475 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20037, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20037, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20038 q = 1) (hb : d127476 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20038, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20038, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9851 q = 1) (hb : d127477 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44080 q ha hb
    | true =>
      simp only [d9851, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44088 q ha hb
  have h5 (q : Pattern) (ha : d20039 q = 1) (hb : d127478 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20039, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20039, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20040 q = 1) (hb : d127479 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20040, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20040, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20041 q = 1) (hb : d127480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20041, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20041, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20046 q = 1) (hb : d127485 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20046, d127485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20046, d127485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20047 q = 1) (hb : d127486 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20047, d127486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20047, d127486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h11 (q : Pattern) (ha : d9835 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9836 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h14 (q : Pattern) (ha : d9852 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9853 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9854 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9859 q = 1) (hb : d101380 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9859, d101380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9859, d101380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9860 q = 1) (hb : d101381 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9860, d101381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9860, d101381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d20048 q = 1) (hb : d130679 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20048, d130679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20048, d130679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro44091 (p : Pattern) (ha : d20054 p = 1) (hb : d130685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20044 q = 1) (hb : d130677 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20044, d130677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44089 q ha hb
    | true =>
      simp only [d20044, d130677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20045 q = 1) (hb : d130678 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20045, d130678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20045, d130678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20049 q = 1) (hb : d130680 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20049, d130680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44090 q ha hb
    | true =>
      simp only [d20049, d130680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20050 q = 1) (hb : d130681 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20050, d130681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20050, d130681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20051 q = 1) (hb : d130682 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20051, d130682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20051, d130682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20052 q = 1) (hb : d130683 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20052, d130683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20052, d130683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20053 q = 1) (hb : d130684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20053, d130684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20053, d130684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20054 q = 1) (hb : d130685 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20054, d130685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20054, d130685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44092 (p : Pattern) (ha : d20065 p = 1) (hb : d130692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20049 q = 1) (hb : d130680 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20049, d130680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44090 q ha hb
    | true =>
      simp only [d20049, d130680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20050 q = 1) (hb : d130681 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20050, d130681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20050, d130681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20060 q = 1) (hb : d130687 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20060, d130687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44082 q ha hb
    | true =>
      simp only [d20060, d130687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20061 q = 1) (hb : d130688 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20061, d130688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20061, d130688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20062 q = 1) (hb : d130689 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20062, d130689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20062, d130689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20063 q = 1) (hb : d130690 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20063, d130690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20063, d130690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20064 q = 1) (hb : d130691 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20064, d130691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20064, d130691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20065 q = 1) (hb : d130692 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20065, d130692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20065, d130692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44093 (p : Pattern) (ha : d9987 p = 1) (hb : d113482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9829 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9829, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9829, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1122 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9830 q = 1) (hb : d52881 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9830, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9830, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9831 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9831, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9831, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9868 q = 1) (hb : d52888 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9868, d52888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9868, d52888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d9987 q = 1) (hb : d113482 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9987, d113482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9987, d113482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro44094 (p : Pattern) (ha : d20097 p = 1) (hb : d130707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9834 q = 1) (hb : d127474 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44086 q ha hb
    | true =>
      simp only [d9834, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44080 q ha hb
  have h2 (q : Pattern) (ha : d20037 q = 1) (hb : d127475 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20037, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20037, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20038 q = 1) (hb : d127476 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20038, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20038, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9851 q = 1) (hb : d127477 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44080 q ha hb
    | true =>
      simp only [d9851, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44088 q ha hb
  have h5 (q : Pattern) (ha : d20039 q = 1) (hb : d127478 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20039, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20039, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20040 q = 1) (hb : d127479 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20040, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20040, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20041 q = 1) (hb : d127480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20041, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20041, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9988 q = 1) (hb : d127521 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9988, d127521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44080 q ha hb
    | true =>
      simp only [d9988, d127521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44093 q ha hb
  have h9 (q : Pattern) (ha : d20093 q = 1) (hb : d127522 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20093, d127522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20093, d127522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20094 q = 1) (hb : d127523 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20094, d127523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20094, d127523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20095 q = 1) (hb : d127524 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20095, d127524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20095, d127524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d20096 q = 1) (hb : d127525 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20096, d127525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20096, d127525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h14 (q : Pattern) (ha : d9835 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9836 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h17 (q : Pattern) (ha : d9852 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9853 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9854 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9988 q = 1) (hb : d101419 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9988, d101419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9988, d101419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23324 q ha hb
  have h21 (q : Pattern) (ha : d9989 q = 1) (hb : d101420 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9989, d101420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9989, d101420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d9990 q = 1) (hb : d101421 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9990, d101421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9990, d101421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9991 q = 1) (hb : d101422 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9991, d101422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9991, d101422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d9992 q = 1) (hb : d101423 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9992, d101423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9992, d101423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d20097 q = 1) (hb : d130707 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20097, d130707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d20097, d130707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro44095 (p : Pattern) (ha : d20103 p = 1) (hb : d130713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20098 q = 1) (hb : d130708 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20098, d130708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44094 q ha hb
    | true =>
      simp only [d20098, d130708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20099 q = 1) (hb : d130709 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20099, d130709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20099, d130709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20100 q = 1) (hb : d130710 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20100, d130710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20100, d130710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20101 q = 1) (hb : d130711 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20101, d130711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20101, d130711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20102 q = 1) (hb : d130712 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20102, d130712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20102, d130712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20103 q = 1) (hb : d130713 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20103, d130713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20103, d130713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44096 (p : Pattern) (ha : d130285 p = 1) (hb : d130719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20066 q = 1) (hb : d130693 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20066, d130693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44091 q ha hb
    | true =>
      simp only [d20066, d130693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44092 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130705 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130281 q = 1) (hb : d130706 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130281, d130706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130281, d130706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20104 q = 1) (hb : d130714 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20104, d130714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44095 q ha hb
    | true =>
      simp only [d20104, d130714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20105 q = 1) (hb : d130715 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20105, d130715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20105, d130715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130282 q = 1) (hb : d130716 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130282, d130716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130282, d130716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130283 q = 1) (hb : d130717 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130283, d130717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130283, d130717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130284 q = 1) (hb : d130718 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130284, d130718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130284, d130718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130285 q = 1) (hb : d130719 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130285, d130719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130285, d130719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro44097 (p : Pattern) (ha : d130291 p = 1) (hb : d130732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130286 q = 1) (hb : d130720 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130286, d130720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130286, d130720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44096 q ha hb
  have h2 (q : Pattern) (ha : d20121 q = 1) (hb : d130727 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20121, d130727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20121, d130727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44084 q ha hb
  have h3 (q : Pattern) (ha : d130287 q = 1) (hb : d130728 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130287, d130728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130287, d130728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130288 q = 1) (hb : d130729 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130288, d130729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130288, d130729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130289 q = 1) (hb : d130730 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130289, d130730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130289, d130730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130290 q = 1) (hb : d130731 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130290, d130731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130290, d130731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130291 q = 1) (hb : d130732 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130291, d130732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130291, d130732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44098 (p : Pattern) (ha : d130297 p = 1) (hb : d130738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130292 q = 1) (hb : d130733 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130292, d130733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130292, d130733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44097 q ha hb
  have h2 (q : Pattern) (ha : d130293 q = 1) (hb : d130734 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130293, d130734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130293, d130734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130294 q = 1) (hb : d130735 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130294, d130735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130294, d130735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130295 q = 1) (hb : d130736 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130295, d130736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130295, d130736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130296 q = 1) (hb : d130737 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130296, d130737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130296, d130737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130297 q = 1) (hb : d130738 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130297, d130738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130297, d130738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44099 (p : Pattern) (ha : d10121 p = 1) (hb : d127766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10111 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10111, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10111, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1571 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d10112 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10112, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10112, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10113 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10113, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10113, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d127761 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10115 q = 1) (hb : d101542 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, d101542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23331 q ha hb
    | true =>
      simp only [d10115, d101542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d10116 q = 1) (hb : d127762 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10116, d127762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10116, d127762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10117 q = 1) (hb : d101544 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10117, d101544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10117, d101544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d10118 q = 1) (hb : d127763 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10118, d127763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10118, d127763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10119 q = 1) (hb : d127764 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10119, d127764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10119, d127764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d10120 q = 1) (hb : d127765 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10120, d127765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10120, d127765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123436 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d10085 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d10086 q = 1) (hb : d123437 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10086, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10086, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10087 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d10088 q = 1) (hb : d123438 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10088, d123438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10088, d123438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10089 q = 1) (hb : d123439 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10089, d123439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10089, d123439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d10105 q = 1) (hb : d123440 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10105, d123440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10105, d123440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h21 (q : Pattern) (ha : d10121 q = 1) (hb : d127766 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10121, d127766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10121, d127766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro44100 (p : Pattern) (ha : d10163 p = 1) (hb : d123474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10159 q = 1) (hb : d53195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10159, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10159, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1583 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d10160 q = 1) (hb : d53196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10160, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10160, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10161 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10161, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10161, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10162 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10162, d53203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10162, d53203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123451 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10135 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d10136 q = 1) (hb : d123452 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10136, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10136, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10137 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d10138 q = 1) (hb : d123453 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10138, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10138, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10139 q = 1) (hb : d123454 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10139, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10139, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d10140 q = 1) (hb : d123455 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10140, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10140, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d10163 q = 1) (hb : d123474 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10163, d123474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10163, d123474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro44101 (p : Pattern) (ha : d20163 p = 1) (hb : d130752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10164 q = 1) (hb : d127787 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, d127787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44099 q ha hb
    | true =>
      simp only [d10164, d127787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44100 q ha hb
  have h2 (q : Pattern) (ha : d20159 q = 1) (hb : d127788 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20159, d127788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20159, d127788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20160 q = 1) (hb : d127789 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20160, d127789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20160, d127789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20161 q = 1) (hb : d127790 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20161, d127790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20161, d127790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20162 q = 1) (hb : d127791 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20162, d127791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20162, d127791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10164 q = 1) (hb : d101591 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23334 q ha hb
  have h7 (q : Pattern) (ha : d10165 q = 1) (hb : d101592 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10166 q = 1) (hb : d101593 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10167 q = 1) (hb : d101594 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10168 q = 1) (hb : d101595 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10168, d101595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10168, d101595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20163 q = 1) (hb : d130752 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20163, d130752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20163, d130752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro44102 (p : Pattern) (ha : d20218 p = 1) (hb : d130770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20164 q = 1) (hb : d130753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20164, d130753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44101 q ha hb
    | true =>
      simp only [d20164, d130753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20165 q = 1) (hb : d130754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20165, d130754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20165, d130754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20215 q = 1) (hb : d130767 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20215, d130767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20215, d130767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20216 q = 1) (hb : d130768 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20216, d130768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20216, d130768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20217 q = 1) (hb : d130769 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20217, d130769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20217, d130769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20218 q = 1) (hb : d130770 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20218, d130770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20218, d130770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44103 (p : Pattern) (ha : d20224 p = 1) (hb : d130792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20219 q = 1) (hb : d130787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20219, d130787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44102 q ha hb
    | true =>
      simp only [d20219, d130787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20220 q = 1) (hb : d130788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20220, d130788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20220, d130788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20221 q = 1) (hb : d130789 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20221, d130789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20221, d130789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20222 q = 1) (hb : d130790 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20222, d130790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20222, d130790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20223 q = 1) (hb : d130791 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20223, d130791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20223, d130791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20224 q = 1) (hb : d130792 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20224, d130792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20224, d130792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44104 (p : Pattern) (ha : d10069 p = 1) (hb : d127744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53179 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1665 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro230 q ha hb
    | true =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10032 q = 1) (hb : d53180 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10032, d53180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10032, d53180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1666 q = 1) (hb : d53107 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d10033 q = 1) (hb : d53181 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10033, d53181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10033, d53181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10034 q = 1) (hb : d53182 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10034, d53182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10034, d53182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d127738 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10036 q = 1) (hb : d101463 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23338 q ha hb
    | true =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d10037 q = 1) (hb : d127739 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10037, d127739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10037, d127739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10038 q = 1) (hb : d101465 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d10039 q = 1) (hb : d127740 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10039, d127740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10039, d127740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10040 q = 1) (hb : d127741 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10040, d127741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10040, d127741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d10041 q = 1) (hb : d127742 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10041, d127742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10041, d127742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123419 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d10046 q = 1) (hb : d101473 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23339 q ha hb
    | true =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d10047 q = 1) (hb : d123420 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10047, d123420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10047, d123420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10048 q = 1) (hb : d101475 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d10049 q = 1) (hb : d123421 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10049, d123421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10049, d123421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10050 q = 1) (hb : d123422 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10050, d123422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10050, d123422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d123426 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d10063 q = 1) (hb : d101490 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23341 q ha hb
    | true =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d10064 q = 1) (hb : d123427 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10064, d123427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10064, d123427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10065 q = 1) (hb : d101492 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d10066 q = 1) (hb : d123428 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10066, d123428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10066, d123428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d10067 q = 1) (hb : d123429 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10067, d123429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d10067, d123429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h26 (q : Pattern) (ha : d10068 q = 1) (hb : d127743 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10068, d127743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10068, d127743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d10069 q = 1) (hb : d127744 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10069, d127744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10069, d127744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro44105 (p : Pattern) (ha : d10091 p = 1) (hb : d127751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53183 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1555 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10070 q = 1) (hb : d53184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10070, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10070, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1556 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d10071 q = 1) (hb : d53185 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10071, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10071, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10072 q = 1) (hb : d53186 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10072, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10072, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d127745 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10074 q = 1) (hb : d101501 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10074, d101501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23343 q ha hb
    | true =>
      simp only [d10074, d101501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d10075 q = 1) (hb : d127746 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10075, d127746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10075, d127746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10076 q = 1) (hb : d101503 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10076, d101503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10076, d101503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d10077 q = 1) (hb : d127747 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10077, d127747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10077, d127747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10078 q = 1) (hb : d127748 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10078, d127748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10078, d127748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d10079 q = 1) (hb : d127749 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10079, d127749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10079, d127749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123426 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d10063 q = 1) (hb : d101490 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23341 q ha hb
    | true =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d10064 q = 1) (hb : d123427 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10064, d123427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10064, d123427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10065 q = 1) (hb : d101492 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d10066 q = 1) (hb : d123428 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10066, d123428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10066, d123428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10067 q = 1) (hb : d123429 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10067, d123429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10067, d123429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d123436 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d10085 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d10086 q = 1) (hb : d123437 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10086, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10086, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10087 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d10088 q = 1) (hb : d123438 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10088, d123438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10088, d123438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d10089 q = 1) (hb : d123439 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10089, d123439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d10089, d123439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h26 (q : Pattern) (ha : d10090 q = 1) (hb : d127750 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10090, d127750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10090, d127750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d10091 q = 1) (hb : d127751 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10091, d127751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10091, d127751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro44106 (p : Pattern) (ha : d10106 p = 1) (hb : d127756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113708 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10099 q = 1) (hb : d101526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23345 q ha hb
    | true =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10100 q = 1) (hb : d113709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10100, d113709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10100, d113709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10101 q = 1) (hb : d101528 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10101, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d10102 q = 1) (hb : d113710 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10102, d113710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10102, d113710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10103 q = 1) (hb : d113711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10103, d113711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10103, d113711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d123436 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10085 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d10086 q = 1) (hb : d123437 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10086, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10086, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10087 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d10088 q = 1) (hb : d123438 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10088, d123438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10088, d123438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10089 q = 1) (hb : d123439 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10089, d123439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10089, d123439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d10104 q = 1) (hb : d127755 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10104, d127755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10104, d127755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10105 q = 1) (hb : d123440 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10105, d123440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10105, d123440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d10106 q = 1) (hb : d127756 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10106, d127756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10106, d127756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro44107 (p : Pattern) (ha : d10141 p = 1) (hb : d123456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76225 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5134 q = 1) (hb : d69221 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7964 q ha hb
    | true =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10125 q = 1) (hb : d76226 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10125, d76226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10125, d76226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5135 q = 1) (hb : d69222 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, d69222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5135, d69222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d10126 q = 1) (hb : d76227 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10126, d76227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10126, d76227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10127 q = 1) (hb : d76228 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10127, d76228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10127, d76228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10128 q = 1) (hb : d76229 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10128, d76229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10128, d76229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123451 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10135 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d10136 q = 1) (hb : d123452 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10136, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10136, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10137 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d10138 q = 1) (hb : d123453 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10138, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10138, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10139 q = 1) (hb : d123454 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10139, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10139, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d10140 q = 1) (hb : d123455 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10140, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10140, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d10141 q = 1) (hb : d123456 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10141, d123456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10141, d123456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro44108 (p : Pattern) (ha : d20147 p = 1) (hb : d130742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10092 q = 1) (hb : d127752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10092, d127752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44104 q ha hb
    | true =>
      simp only [d10092, d127752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44105 q ha hb
  have h2 (q : Pattern) (ha : d20136 q = 1) (hb : d127753 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20136, d127753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20136, d127753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20137 q = 1) (hb : d127754 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20137, d127754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20137, d127754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10107 q = 1) (hb : d127757 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10107, d127757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44105 q ha hb
    | true =>
      simp only [d10107, d127757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44106 q ha hb
  have h5 (q : Pattern) (ha : d20138 q = 1) (hb : d127758 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20138, d127758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20138, d127758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20139 q = 1) (hb : d127759 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20139, d127759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20139, d127759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20140 q = 1) (hb : d127760 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20140, d127760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20140, d127760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10122 q = 1) (hb : d127767 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44105 q ha hb
    | true =>
      simp only [d10122, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44099 q ha hb
  have h9 (q : Pattern) (ha : d20141 q = 1) (hb : d127768 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20141, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20141, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20142 q = 1) (hb : d127769 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20142, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20142, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10142 q = 1) (hb : d127770 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44099 q ha hb
    | true =>
      simp only [d10142, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44107 q ha hb
  have h12 (q : Pattern) (ha : d20143 q = 1) (hb : d127771 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20143, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20143, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20144 q = 1) (hb : d127772 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20144, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20144, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d20145 q = 1) (hb : d127773 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20145, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20145, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d20146 q = 1) (hb : d127774 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20146, d127774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20146, d127774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10092 q = 1) (hb : d101519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10092, d101519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23342 q ha hb
    | true =>
      simp only [d10092, d101519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
  have h17 (q : Pattern) (ha : d10093 q = 1) (hb : d101520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10093, d101520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10093, d101520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10094 q = 1) (hb : d101521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10094, d101521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10094, d101521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10107 q = 1) (hb : d101534 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10107, d101534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10107, d101534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23346 q ha hb
  have h20 (q : Pattern) (ha : d10108 q = 1) (hb : d101535 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10108, d101535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10108, d101535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d10109 q = 1) (hb : d101536 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10109, d101536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10109, d101536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d10110 q = 1) (hb : d101537 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10110, d101537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10110, d101537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h24 (q : Pattern) (ha : d10123 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d10124 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h27 (q : Pattern) (ha : d10143 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d10144 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d10145 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d10146 q = 1) (hb : d101573 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10146, d101573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10146, d101573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d20147 q = 1) (hb : d130742 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20147, d130742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20147, d130742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro44109 (p : Pattern) (ha : d20152 p = 1) (hb : d130745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10122 q = 1) (hb : d127767 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44105 q ha hb
    | true =>
      simp only [d10122, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44099 q ha hb
  have h2 (q : Pattern) (ha : d20141 q = 1) (hb : d127768 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20141, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20141, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20142 q = 1) (hb : d127769 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20142, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20142, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10142 q = 1) (hb : d127770 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44099 q ha hb
    | true =>
      simp only [d10142, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44107 q ha hb
  have h5 (q : Pattern) (ha : d20143 q = 1) (hb : d127771 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20143, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20143, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20144 q = 1) (hb : d127772 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20144, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20144, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20145 q = 1) (hb : d127773 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20145, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20145, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20150 q = 1) (hb : d127778 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20150, d127778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20150, d127778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20151 q = 1) (hb : d127779 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20151, d127779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20151, d127779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h11 (q : Pattern) (ha : d10123 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10124 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h14 (q : Pattern) (ha : d10143 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10144 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10145 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10150 q = 1) (hb : d101577 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10150, d101577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10150, d101577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10151 q = 1) (hb : d101578 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10151, d101578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10151, d101578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d20152 q = 1) (hb : d130745 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20152, d130745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20152, d130745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro44110 (p : Pattern) (ha : d20158 p = 1) (hb : d130751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20148 q = 1) (hb : d130743 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20148, d130743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44108 q ha hb
    | true =>
      simp only [d20148, d130743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20149 q = 1) (hb : d130744 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20149, d130744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20149, d130744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20153 q = 1) (hb : d130746 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20153, d130746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44109 q ha hb
    | true =>
      simp only [d20153, d130746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20154 q = 1) (hb : d130747 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20154, d130747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20154, d130747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20155 q = 1) (hb : d130748 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20155, d130748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20155, d130748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20156 q = 1) (hb : d130749 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20156, d130749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20156, d130749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20157 q = 1) (hb : d130750 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20157, d130750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20157, d130750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20158 q = 1) (hb : d130751 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20158, d130751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20158, d130751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44111 (p : Pattern) (ha : d20169 p = 1) (hb : d130758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20153 q = 1) (hb : d130746 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20153, d130746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44109 q ha hb
    | true =>
      simp only [d20153, d130746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20154 q = 1) (hb : d130747 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20154, d130747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20154, d130747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20164 q = 1) (hb : d130753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20164, d130753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44101 q ha hb
    | true =>
      simp only [d20164, d130753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20165 q = 1) (hb : d130754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20165, d130754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20165, d130754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20166 q = 1) (hb : d130755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20166, d130755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20166, d130755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20167 q = 1) (hb : d130756 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20167, d130756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20167, d130756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20168 q = 1) (hb : d130757 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20168, d130757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20168, d130757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20169 q = 1) (hb : d130758 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20169, d130758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20169, d130758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44112 (p : Pattern) (ha : d10293 p = 1) (hb : d113738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10159 q = 1) (hb : d53195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10159, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10159, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1583 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d10160 q = 1) (hb : d53196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10160, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10160, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10161 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10161, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10161, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10162 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10162, d53203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10162, d53203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d10293 q = 1) (hb : d113738 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10293, d113738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10293, d113738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro44113 (p : Pattern) (ha : d20201 p = 1) (hb : d130773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10122 q = 1) (hb : d127767 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44105 q ha hb
    | true =>
      simp only [d10122, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44099 q ha hb
  have h2 (q : Pattern) (ha : d20141 q = 1) (hb : d127768 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20141, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20141, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20142 q = 1) (hb : d127769 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20142, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20142, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10142 q = 1) (hb : d127770 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44099 q ha hb
    | true =>
      simp only [d10142, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44107 q ha hb
  have h5 (q : Pattern) (ha : d20143 q = 1) (hb : d127771 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20143, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20143, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20144 q = 1) (hb : d127772 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20144, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20144, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20145 q = 1) (hb : d127773 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20145, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20145, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10294 q = 1) (hb : d127814 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10294, d127814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44099 q ha hb
    | true =>
      simp only [d10294, d127814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44112 q ha hb
  have h9 (q : Pattern) (ha : d20197 q = 1) (hb : d127815 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20197, d127815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20197, d127815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20198 q = 1) (hb : d127816 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20198, d127816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20198, d127816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20199 q = 1) (hb : d127817 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20199, d127817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20199, d127817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d20200 q = 1) (hb : d127818 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20200, d127818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20200, d127818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h14 (q : Pattern) (ha : d10123 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10124 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h17 (q : Pattern) (ha : d10143 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10144 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10145 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10294 q = 1) (hb : d101619 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10294, d101619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10294, d101619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23352 q ha hb
  have h21 (q : Pattern) (ha : d10295 q = 1) (hb : d101620 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10295, d101620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10295, d101620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10296 q = 1) (hb : d101621 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10296, d101621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10296, d101621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10297 q = 1) (hb : d101622 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10297, d101622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10297, d101622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d10298 q = 1) (hb : d101623 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10298, d101623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10298, d101623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d20201 q = 1) (hb : d130773 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20201, d130773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d20201, d130773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro44114 (p : Pattern) (ha : d20207 p = 1) (hb : d130779 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20202 q = 1) (hb : d130774 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20202, d130774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44113 q ha hb
    | true =>
      simp only [d20202, d130774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20203 q = 1) (hb : d130775 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20203, d130775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20203, d130775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20204 q = 1) (hb : d130776 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20204, d130776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20204, d130776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20205 q = 1) (hb : d130777 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20205, d130777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20205, d130777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20206 q = 1) (hb : d130778 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20206, d130778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20206, d130778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20207 q = 1) (hb : d130779 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20207, d130779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20207, d130779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44115 (p : Pattern) (ha : d130305 p = 1) (hb : d130785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20170 q = 1) (hb : d130759 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20170, d130759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44110 q ha hb
    | true =>
      simp only [d20170, d130759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44111 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130771 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130301 q = 1) (hb : d130772 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130301, d130772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130301, d130772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20208 q = 1) (hb : d130780 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20208, d130780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44114 q ha hb
    | true =>
      simp only [d20208, d130780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20209 q = 1) (hb : d130781 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20209, d130781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20209, d130781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130302 q = 1) (hb : d130782 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130302, d130782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130302, d130782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130303 q = 1) (hb : d130783 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130303, d130783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130303, d130783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130304 q = 1) (hb : d130784 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130304, d130784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130304, d130784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130305 q = 1) (hb : d130785 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130305, d130785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130305, d130785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro44116 (p : Pattern) (ha : d130311 p = 1) (hb : d130798 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130306 q = 1) (hb : d130786 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130306, d130786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130306, d130786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44115 q ha hb
  have h2 (q : Pattern) (ha : d20225 q = 1) (hb : d130793 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20225, d130793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20225, d130793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44103 q ha hb
  have h3 (q : Pattern) (ha : d130307 q = 1) (hb : d130794 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130307, d130794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130307, d130794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130308 q = 1) (hb : d130795 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130308, d130795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130308, d130795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130309 q = 1) (hb : d130796 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130309, d130796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130309, d130796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130310 q = 1) (hb : d130797 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130310, d130797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130310, d130797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130311 q = 1) (hb : d130798 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130311, d130798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130311, d130798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44117 (p : Pattern) (ha : d130317 p = 1) (hb : d130804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130312 q = 1) (hb : d130799 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130312, d130799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130312, d130799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44116 q ha hb
  have h2 (q : Pattern) (ha : d130313 q = 1) (hb : d130800 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130313, d130800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130313, d130800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130314 q = 1) (hb : d130801 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130314, d130801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130314, d130801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130315 q = 1) (hb : d130802 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130315, d130802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130315, d130802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130316 q = 1) (hb : d130803 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130316, d130803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130316, d130803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130317 q = 1) (hb : d130804 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130317, d130804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130317, d130804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44118 (p : Pattern) (ha : d10397 p = 1) (hb : d128058 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10387 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10387, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10387, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2054 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d10388 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10388, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10388, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10389 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10389, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10389, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d128053 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10391 q = 1) (hb : d101712 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10391, d101712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23359 q ha hb
    | true =>
      simp only [d10391, d101712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d10392 q = 1) (hb : d128054 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10392, d128054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10392, d128054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10393 q = 1) (hb : d101714 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10393, d101714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10393, d101714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d10394 q = 1) (hb : d128055 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10394, d128055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10394, d128055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10395 q = 1) (hb : d128056 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10395, d128056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10395, d128056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d10396 q = 1) (hb : d128057 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10396, d128057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10396, d128057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d10371 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d10372 q = 1) (hb : d123729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10372, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10372, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10373 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d10374 q = 1) (hb : d123730 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10374, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10374, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10375 q = 1) (hb : d123731 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10375, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10375, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d10381 q = 1) (hb : d123732 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10381, d123732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10381, d123732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h21 (q : Pattern) (ha : d10397 q = 1) (hb : d128058 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10397, d128058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10397, d128058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro44119 (p : Pattern) (ha : d10440 p = 1) (hb : d123766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10436 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10436, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10436, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2066 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d10437 q = 1) (hb : d53513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10437, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10437, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10438 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10438, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10438, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10439 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10439, d53520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10439, d53520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d10413 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10413, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10413, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10414 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d10415 q = 1) (hb : d123745 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10415, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10415, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10416 q = 1) (hb : d123746 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10416, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10416, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d10417 q = 1) (hb : d123747 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10417, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10417, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d10440 q = 1) (hb : d123766 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10440, d123766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10440, d123766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro44120 (p : Pattern) (ha : d20268 p = 1) (hb : d130819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10441 q = 1) (hb : d128079 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, d128079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44118 q ha hb
    | true =>
      simp only [d10441, d128079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44119 q ha hb
  have h2 (q : Pattern) (ha : d20264 q = 1) (hb : d128080 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20264, d128080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20264, d128080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20265 q = 1) (hb : d128081 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20265, d128081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20265, d128081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20266 q = 1) (hb : d128082 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20266, d128082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20266, d128082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20267 q = 1) (hb : d128083 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20267, d128083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20267, d128083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10441 q = 1) (hb : d101762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23362 q ha hb
  have h7 (q : Pattern) (ha : d10442 q = 1) (hb : d101763 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10443 q = 1) (hb : d101764 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10444 q = 1) (hb : d101765 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10445 q = 1) (hb : d101766 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10445, d101766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10445, d101766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20268 q = 1) (hb : d130819 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20268, d130819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20268, d130819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro44121 (p : Pattern) (ha : d20323 p = 1) (hb : d130837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20269 q = 1) (hb : d130820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20269, d130820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44120 q ha hb
    | true =>
      simp only [d20269, d130820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20270 q = 1) (hb : d130821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20270, d130821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20270, d130821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20320 q = 1) (hb : d130834 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20320, d130834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20320, d130834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20321 q = 1) (hb : d130835 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20321, d130835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20321, d130835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20322 q = 1) (hb : d130836 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20322, d130836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20322, d130836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20323 q = 1) (hb : d130837 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20323, d130837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20323, d130837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44122 (p : Pattern) (ha : d20329 p = 1) (hb : d130859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20324 q = 1) (hb : d130854 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20324, d130854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44121 q ha hb
    | true =>
      simp only [d20324, d130854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20325 q = 1) (hb : d130855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20325, d130855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20325, d130855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20326 q = 1) (hb : d130856 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20326, d130856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20326, d130856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20327 q = 1) (hb : d130857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20327, d130857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20327, d130857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20328 q = 1) (hb : d130858 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20328, d130858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20328, d130858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20329 q = 1) (hb : d130859 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20329, d130859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20329, d130859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44123 (p : Pattern) (ha : d10359 p = 1) (hb : d128037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53496 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2144 q = 1) (hb : d53423 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
    | true =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10339 q = 1) (hb : d53497 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10339, d53497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10339, d53497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2145 q = 1) (hb : d53424 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d10340 q = 1) (hb : d53498 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10340, d53498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10340, d53498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10341 q = 1) (hb : d53499 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10341, d53499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10341, d53499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d128031 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10343 q = 1) (hb : d101664 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
    | true =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d10344 q = 1) (hb : d128032 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10344, d128032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10344, d128032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10345 q = 1) (hb : d101666 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d10346 q = 1) (hb : d128033 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10346, d128033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10346, d128033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10347 q = 1) (hb : d128034 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10347, d128034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10347, d128034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d10348 q = 1) (hb : d128035 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10348, d128035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10348, d128035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d10354 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10354, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10354, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d10356 q = 1) (hb : d113967 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10356, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10356, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10357 q = 1) (hb : d113968 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10357, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10357, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d10358 q = 1) (hb : d128036 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10358, d128036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10358, d128036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10359 q = 1) (hb : d128037 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10359, d128037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10359, d128037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro44124 (p : Pattern) (ha : d10377 p = 1) (hb : d128044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53500 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2035 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10360 q = 1) (hb : d53501 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10360, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10360, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2036 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d10361 q = 1) (hb : d53502 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10361, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10361, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10362 q = 1) (hb : d53503 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10362, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10362, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d128038 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10364 q = 1) (hb : d101685 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
    | true =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d10365 q = 1) (hb : d128039 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10365, d128039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10365, d128039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10366 q = 1) (hb : d101687 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d10367 q = 1) (hb : d128040 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10367, d128040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10367, d128040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10368 q = 1) (hb : d128041 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10368, d128041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10368, d128041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d10369 q = 1) (hb : d128042 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10369, d128042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10369, d128042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d10354 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10354, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10354, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d10356 q = 1) (hb : d113967 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10356, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10356, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10357 q = 1) (hb : d113968 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10357, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10357, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d10371 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d10372 q = 1) (hb : d123729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10372, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10372, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10373 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d10374 q = 1) (hb : d123730 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10374, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10374, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d10375 q = 1) (hb : d123731 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10375, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d10375, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h26 (q : Pattern) (ha : d10376 q = 1) (hb : d128043 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10376, d128043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10376, d128043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d10377 q = 1) (hb : d128044 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10377, d128044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10377, d128044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro44125 (p : Pattern) (ha : d10382 p = 1) (hb : d128048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10354 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10354, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10354, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d10356 q = 1) (hb : d113967 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10356, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10356, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10357 q = 1) (hb : d113968 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10357, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10357, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10371 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d10372 q = 1) (hb : d123729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10372, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10372, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10373 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d10374 q = 1) (hb : d123730 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10374, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10374, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10375 q = 1) (hb : d123731 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10375, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10375, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d10376 q = 1) (hb : d128043 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10376, d128043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10376, d128043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10381 q = 1) (hb : d123732 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10381, d123732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10381, d123732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d10382 q = 1) (hb : d128048 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10382, d128048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10382, d128048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro44126 (p : Pattern) (ha : d10418 p = 1) (hb : d123748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76361 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5247 q = 1) (hb : d69331 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7980 q ha hb
    | true =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10401 q = 1) (hb : d76362 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10401, d76362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10401, d76362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5248 q = 1) (hb : d69332 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5248, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5248, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d10402 q = 1) (hb : d76363 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10402, d76363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10402, d76363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10403 q = 1) (hb : d76364 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10403, d76364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10403, d76364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10404 q = 1) (hb : d76365 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10404, d76365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10404, d76365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d10413 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10413, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10413, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10414 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d10415 q = 1) (hb : d123745 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10415, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10415, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10416 q = 1) (hb : d123746 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10416, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10416, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d10417 q = 1) (hb : d123747 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10417, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10417, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d10418 q = 1) (hb : d123748 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10418, d123748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10418, d123748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro44127 (p : Pattern) (ha : d20252 p = 1) (hb : d130809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10378 q = 1) (hb : d128045 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10378, d128045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44123 q ha hb
    | true =>
      simp only [d10378, d128045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44124 q ha hb
  have h2 (q : Pattern) (ha : d20241 q = 1) (hb : d128046 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20241, d128046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20241, d128046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20242 q = 1) (hb : d128047 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20242, d128047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20242, d128047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10383 q = 1) (hb : d128049 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10383, d128049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44124 q ha hb
    | true =>
      simp only [d10383, d128049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44125 q ha hb
  have h5 (q : Pattern) (ha : d20243 q = 1) (hb : d128050 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20243, d128050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20243, d128050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20244 q = 1) (hb : d128051 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20244, d128051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20244, d128051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20245 q = 1) (hb : d128052 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20245, d128052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20245, d128052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10398 q = 1) (hb : d128059 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44124 q ha hb
    | true =>
      simp only [d10398, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44118 q ha hb
  have h9 (q : Pattern) (ha : d20246 q = 1) (hb : d128060 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20246, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20246, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20247 q = 1) (hb : d128061 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20247, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20247, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10419 q = 1) (hb : d128062 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44118 q ha hb
    | true =>
      simp only [d10419, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44126 q ha hb
  have h12 (q : Pattern) (ha : d20248 q = 1) (hb : d128063 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20248, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20248, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20249 q = 1) (hb : d128064 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20249, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20249, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d20250 q = 1) (hb : d128065 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20250, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20250, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d20251 q = 1) (hb : d128066 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20251, d128066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20251, d128066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10378 q = 1) (hb : d101699 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10378, d101699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23368 q ha hb
    | true =>
      simp only [d10378, d101699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
  have h17 (q : Pattern) (ha : d10379 q = 1) (hb : d101700 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10379, d101700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10379, d101700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10380 q = 1) (hb : d101701 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10380, d101701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10380, d101701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10383 q = 1) (hb : d101704 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10383, d101704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10383, d101704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23371 q ha hb
  have h20 (q : Pattern) (ha : d10384 q = 1) (hb : d101705 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10384, d101705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10384, d101705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d10385 q = 1) (hb : d101706 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10385, d101706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10385, d101706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d10386 q = 1) (hb : d101707 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10386, d101707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10386, d101707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h24 (q : Pattern) (ha : d10399 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d10400 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h27 (q : Pattern) (ha : d10420 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d10421 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d10422 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d10423 q = 1) (hb : d101744 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10423, d101744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10423, d101744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d20252 q = 1) (hb : d130809 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20252, d130809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20252, d130809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro44128 (p : Pattern) (ha : d20257 p = 1) (hb : d130812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10398 q = 1) (hb : d128059 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44124 q ha hb
    | true =>
      simp only [d10398, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44118 q ha hb
  have h2 (q : Pattern) (ha : d20246 q = 1) (hb : d128060 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20246, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20246, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20247 q = 1) (hb : d128061 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20247, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20247, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10419 q = 1) (hb : d128062 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44118 q ha hb
    | true =>
      simp only [d10419, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44126 q ha hb
  have h5 (q : Pattern) (ha : d20248 q = 1) (hb : d128063 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20248, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20248, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20249 q = 1) (hb : d128064 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20249, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20249, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20250 q = 1) (hb : d128065 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20250, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20250, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20255 q = 1) (hb : d128070 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20255, d128070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20255, d128070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20256 q = 1) (hb : d128071 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20256, d128071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20256, d128071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h11 (q : Pattern) (ha : d10399 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10400 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h14 (q : Pattern) (ha : d10420 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10421 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10422 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10427 q = 1) (hb : d101748 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10427, d101748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10427, d101748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10428 q = 1) (hb : d101749 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10428, d101749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10428, d101749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d20257 q = 1) (hb : d130812 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20257, d130812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20257, d130812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro44129 (p : Pattern) (ha : d20263 p = 1) (hb : d130818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20253 q = 1) (hb : d130810 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20253, d130810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44127 q ha hb
    | true =>
      simp only [d20253, d130810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20254 q = 1) (hb : d130811 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20254, d130811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20254, d130811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20258 q = 1) (hb : d130813 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20258, d130813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44128 q ha hb
    | true =>
      simp only [d20258, d130813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20259 q = 1) (hb : d130814 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20259, d130814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20259, d130814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20260 q = 1) (hb : d130815 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20260, d130815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20260, d130815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20261 q = 1) (hb : d130816 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20261, d130816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20261, d130816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20262 q = 1) (hb : d130817 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20262, d130817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20262, d130817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20263 q = 1) (hb : d130818 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20263, d130818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20263, d130818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44130 (p : Pattern) (ha : d20274 p = 1) (hb : d130825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20258 q = 1) (hb : d130813 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20258, d130813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44128 q ha hb
    | true =>
      simp only [d20258, d130813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20259 q = 1) (hb : d130814 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20259, d130814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20259, d130814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20269 q = 1) (hb : d130820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20269, d130820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44120 q ha hb
    | true =>
      simp only [d20269, d130820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20270 q = 1) (hb : d130821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20270, d130821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20270, d130821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20271 q = 1) (hb : d130822 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20271, d130822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20271, d130822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20272 q = 1) (hb : d130823 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20272, d130823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20272, d130823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20273 q = 1) (hb : d130824 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20273, d130824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20273, d130824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20274 q = 1) (hb : d130825 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20274, d130825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20274, d130825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44131 (p : Pattern) (ha : d10559 p = 1) (hb : d113995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10436 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10436, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10436, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2066 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d10437 q = 1) (hb : d53513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10437, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10437, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10438 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10438, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10438, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10439 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10439, d53520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10439, d53520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d10559 q = 1) (hb : d113995 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10559, d113995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10559, d113995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro44132 (p : Pattern) (ha : d20306 p = 1) (hb : d130840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10398 q = 1) (hb : d128059 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44124 q ha hb
    | true =>
      simp only [d10398, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44118 q ha hb
  have h2 (q : Pattern) (ha : d20246 q = 1) (hb : d128060 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20246, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20246, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20247 q = 1) (hb : d128061 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20247, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20247, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10419 q = 1) (hb : d128062 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44118 q ha hb
    | true =>
      simp only [d10419, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44126 q ha hb
  have h5 (q : Pattern) (ha : d20248 q = 1) (hb : d128063 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20248, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20248, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20249 q = 1) (hb : d128064 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20249, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20249, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20250 q = 1) (hb : d128065 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20250, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20250, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10560 q = 1) (hb : d128106 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10560, d128106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44118 q ha hb
    | true =>
      simp only [d10560, d128106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44131 q ha hb
  have h9 (q : Pattern) (ha : d20302 q = 1) (hb : d128107 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20302, d128107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20302, d128107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20303 q = 1) (hb : d128108 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20303, d128108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20303, d128108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20304 q = 1) (hb : d128109 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20304, d128109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20304, d128109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d20305 q = 1) (hb : d128110 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20305, d128110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20305, d128110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h14 (q : Pattern) (ha : d10399 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10400 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h17 (q : Pattern) (ha : d10420 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10421 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10422 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10560 q = 1) (hb : d101790 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10560, d101790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10560, d101790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23377 q ha hb
  have h21 (q : Pattern) (ha : d10561 q = 1) (hb : d101791 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10561, d101791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10561, d101791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10562 q = 1) (hb : d101792 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10562, d101792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10562, d101792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10563 q = 1) (hb : d101793 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10563, d101793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10563, d101793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d10564 q = 1) (hb : d101794 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10564, d101794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10564, d101794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d20306 q = 1) (hb : d130840 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20306, d130840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d20306, d130840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro44133 (p : Pattern) (ha : d20312 p = 1) (hb : d130846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20307 q = 1) (hb : d130841 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20307, d130841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44132 q ha hb
    | true =>
      simp only [d20307, d130841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20308 q = 1) (hb : d130842 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20308, d130842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20308, d130842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20309 q = 1) (hb : d130843 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20309, d130843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20309, d130843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20310 q = 1) (hb : d130844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20310, d130844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20310, d130844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20311 q = 1) (hb : d130845 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20311, d130845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20311, d130845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20312 q = 1) (hb : d130846 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20312, d130846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20312, d130846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44134 (p : Pattern) (ha : d130326 p = 1) (hb : d130852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20275 q = 1) (hb : d130826 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20275, d130826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44129 q ha hb
    | true =>
      simp only [d20275, d130826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44130 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130838 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130322 q = 1) (hb : d130839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130322, d130839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130322, d130839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20313 q = 1) (hb : d130847 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20313, d130847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44133 q ha hb
    | true =>
      simp only [d20313, d130847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20314 q = 1) (hb : d130848 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20314, d130848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20314, d130848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130323 q = 1) (hb : d130849 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130323, d130849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130323, d130849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130324 q = 1) (hb : d130850 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130324, d130850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130324, d130850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130325 q = 1) (hb : d130851 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130325, d130851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130325, d130851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130326 q = 1) (hb : d130852 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130326, d130852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130326, d130852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro44135 (p : Pattern) (ha : d130332 p = 1) (hb : d130865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130327 q = 1) (hb : d130853 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130327, d130853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130327, d130853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44134 q ha hb
  have h2 (q : Pattern) (ha : d20330 q = 1) (hb : d130860 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20330, d130860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20330, d130860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44122 q ha hb
  have h3 (q : Pattern) (ha : d130328 q = 1) (hb : d130861 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130328, d130861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130328, d130861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130329 q = 1) (hb : d130862 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130329, d130862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130329, d130862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130330 q = 1) (hb : d130863 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130330, d130863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130330, d130863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130331 q = 1) (hb : d130864 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130331, d130864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130331, d130864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130332 q = 1) (hb : d130865 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130332, d130865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130332, d130865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44136 (p : Pattern) (ha : d130338 p = 1) (hb : d130871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130333 q = 1) (hb : d130866 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130333, d130866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130333, d130866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44135 q ha hb
  have h2 (q : Pattern) (ha : d130334 q = 1) (hb : d130867 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130334, d130867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130334, d130867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130335 q = 1) (hb : d130868 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130335, d130868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130335, d130868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130336 q = 1) (hb : d130869 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130336, d130869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130336, d130869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130337 q = 1) (hb : d130870 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130337, d130870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130337, d130870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130338 q = 1) (hb : d130871 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130338, d130871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130338, d130871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44137 (p : Pattern) (ha : d130344 p = 1) (hb : d130877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d130261 q = 1) (hb : d130620 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130261, d130620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44050 q ha hb
    | true =>
      simp only [d130261, d130620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44063 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130279 q = 1) (hb : d130674 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130279, d130674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130279, d130674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44079 q ha hb
  have h3 (q : Pattern) (ha : d130280 q = 1) (hb : d130675 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130280, d130675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130280, d130675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130298 q = 1) (hb : d130739 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130298, d130739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130298, d130739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44098 q ha hb
  have h5 (q : Pattern) (ha : d130299 q = 1) (hb : d130740 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130299, d130740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130299, d130740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130300 q = 1) (hb : d130741 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130300, d130741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130300, d130741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130318 q = 1) (hb : d130805 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130318, d130805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130318, d130805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44117 q ha hb
  have h8 (q : Pattern) (ha : d130319 q = 1) (hb : d130806 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130319, d130806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130319, d130806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130320 q = 1) (hb : d130807 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130320, d130807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130320, d130807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130321 q = 1) (hb : d130808 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130321, d130808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130321, d130808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d130339 q = 1) (hb : d130872 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130339, d130872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130339, d130872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44136 q ha hb
  have h12 (q : Pattern) (ha : d130340 q = 1) (hb : d130873 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130340, d130873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130340, d130873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d130341 q = 1) (hb : d130874 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130341, d130874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130341, d130874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d130342 q = 1) (hb : d130875 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130342, d130875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130342, d130875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d130343 q = 1) (hb : d130876 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d130343, d130876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d130343, d130876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d130344 q = 1) (hb : d130877 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d130344, d130877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d130344, d130877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro44138 (p : Pattern) (ha : d130350 p = 1) (hb : d130883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130345 q = 1) (hb : d130878 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d130345, d130878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44137 q ha hb
    | true =>
      simp only [d130345, d130878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d130346 q = 1) (hb : d130879 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d130346, d130879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130346, d130879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d130347 q = 1) (hb : d130880 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d130347, d130880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130347, d130880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d130348 q = 1) (hb : d130881 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d130348, d130881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130348, d130881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130349 q = 1) (hb : d130882 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d130349, d130882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130349, d130882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130350 q = 1) (hb : d130883 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d130350, d130883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130350, d130883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44139 (p : Pattern) (ha : d130356 p = 1) (hb : d130889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130351 q = 1) (hb : d130884 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d130351, d130884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44138 q ha hb
    | true =>
      simp only [d130351, d130884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d130352 q = 1) (hb : d130885 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d130352, d130885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130352, d130885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d130353 q = 1) (hb : d130886 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d130353, d130886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130353, d130886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d130354 q = 1) (hb : d130887 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d130354, d130887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130354, d130887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130355 q = 1) (hb : d130888 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d130355, d130888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130355, d130888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130356 q = 1) (hb : d130889 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d130356, d130889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130356, d130889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44140 (p : Pattern) (ha : d130362 p = 1) (hb : d130895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130357 q = 1) (hb : d130890 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d130357, d130890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44139 q ha hb
    | true =>
      simp only [d130357, d130890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d130358 q = 1) (hb : d130891 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d130358, d130891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130358, d130891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d130359 q = 1) (hb : d130892 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d130359, d130892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130359, d130892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d130360 q = 1) (hb : d130893 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d130360, d130893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130360, d130893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130361 q = 1) (hb : d130894 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d130361, d130894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130361, d130894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130362 q = 1) (hb : d130895 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d130362, d130895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130362, d130895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44141 (p : Pattern) (ha : d130368 p = 1) (hb : d130901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130363 q = 1) (hb : d130896 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d130363, d130896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44140 q ha hb
    | true =>
      simp only [d130363, d130896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d130364 q = 1) (hb : d130897 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d130364, d130897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130364, d130897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d130365 q = 1) (hb : d130898 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d130365, d130898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130365, d130898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d130366 q = 1) (hb : d130899 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d130366, d130899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130366, d130899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130367 q = 1) (hb : d130900 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d130367, d130900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130367, d130900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130368 q = 1) (hb : d130901 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d130368, d130901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130368, d130901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44142 (p : Pattern) (ha : d130374 p = 1) (hb : d130907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130369 q = 1) (hb : d130902 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d130369, d130902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44141 q ha hb
    | true =>
      simp only [d130369, d130902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d130370 q = 1) (hb : d130903 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d130370, d130903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130370, d130903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d130371 q = 1) (hb : d130904 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d130371, d130904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130371, d130904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d130372 q = 1) (hb : d130905 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d130372, d130905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130372, d130905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130373 q = 1) (hb : d130906 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d130373, d130906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130373, d130906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130374 q = 1) (hb : d130907 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d130374, d130907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130374, d130907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44143 (p : Pattern) (ha : d130380 p = 1) (hb : d130913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130375 q = 1) (hb : d130908 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d130375, d130908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44142 q ha hb
    | true =>
      simp only [d130375, d130908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d130376 q = 1) (hb : d130909 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d130376, d130909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130376, d130909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d130377 q = 1) (hb : d130910 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d130377, d130910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130377, d130910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d130378 q = 1) (hb : d130911 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d130378, d130911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130378, d130911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130379 q = 1) (hb : d130912 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d130379, d130912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130379, d130912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130380 q = 1) (hb : d130913 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d130380, d130913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130380, d130913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44144 (p : Pattern) (ha : d130386 p = 1) (hb : d130919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130381 q = 1) (hb : d130914 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d130381, d130914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44143 q ha hb
    | true =>
      simp only [d130381, d130914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d130382 q = 1) (hb : d130915 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d130382, d130915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130382, d130915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d130383 q = 1) (hb : d130916 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d130383, d130916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130383, d130916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d130384 q = 1) (hb : d130917 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d130384, d130917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130384, d130917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130385 q = 1) (hb : d130918 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d130385, d130918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130385, d130918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130386 q = 1) (hb : d130919 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d130386, d130919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130386, d130919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44145 (p : Pattern) (ha : d188723 p = 1) (hb : d190593 p = 1) : d188723 p = 1 := by
  have h0 (q : Pattern) (ha : d188723 q = 1) (hb : d190593 q = 1) : d188723 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro44146 (p : Pattern) (ha : d19845 p = 1) (hb : d130518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130513 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19749 q = 1) (hb : d130490 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19749, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44035 q ha hb
    | true =>
      simp only [d19749, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19841 q = 1) (hb : d130514 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19841, d130514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19841, d130514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130491 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d19842 q = 1) (hb : d130515 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19842, d130515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19842, d130515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19843 q = 1) (hb : d130516 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19843, d130516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19843, d130516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19844 q = 1) (hb : d130517 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19844, d130517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19844, d130517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19845 q = 1) (hb : d130518 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19845, d130518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19845, d130518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44147 (p : Pattern) (ha : d130524 p = 1) (hb : d188529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19846 q = 1) (hb : d130519 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19846, d130519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19846, d130519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44146 q ha hb
  have h2 (q : Pattern) (ha : d130520 q = 1) (hb : d188525 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130520, d188525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130520, d188525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130521 q = 1) (hb : d188526 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130521, d188526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130521, d188526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130522 q = 1) (hb : d188527 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130522, d188527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130522, d188527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130523 q = 1) (hb : d188528 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130523, d188528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130523, d188528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130524 q = 1) (hb : d188529 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130524, d188529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130524, d188529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44148 (p : Pattern) (ha : d130548 p = 1) (hb : d188539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130537 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19776 q = 1) (hb : d130513 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19776, d130513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44040 q ha hb
    | true =>
      simp only [d19776, d130513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44035 q ha hb
  have h3 (q : Pattern) (ha : d130538 q = 1) (hb : d188535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130538, d188535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130538, d188535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130544 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130545 q = 1) (hb : d188536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130545, d188536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130545, d188536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130546 q = 1) (hb : d188537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130546, d188537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130546, d188537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130547 q = 1) (hb : d188538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130547, d188538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130547, d188538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130548 q = 1) (hb : d188539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130548, d188539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130548, d188539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44149 (p : Pattern) (ha : d130560 p = 1) (hb : d188545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130549 q = 1) (hb : d188540 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130549, d188540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130549, d188540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44148 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130555 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130556 q = 1) (hb : d188541 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130556, d188541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130556, d188541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130557 q = 1) (hb : d188542 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130557, d188542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130557, d188542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130558 q = 1) (hb : d188543 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130558, d188543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130558, d188543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130559 q = 1) (hb : d188544 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130559, d188544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130559, d188544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130560 q = 1) (hb : d188545 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130560, d188545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130560, d188545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44150 (p : Pattern) (ha : d130566 p = 1) (hb : d188551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130505 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130525 q = 1) (hb : d188530 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130525, d188530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130525, d188530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44147 q ha hb
  have h3 (q : Pattern) (ha : d130526 q = 1) (hb : d188531 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130526, d188531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130526, d188531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130527 q = 1) (hb : d188532 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130527, d188532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130527, d188532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130528 q = 1) (hb : d188533 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130528, d188533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130528, d188533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130529 q = 1) (hb : d188534 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130529, d188534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130529, d188534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130561 q = 1) (hb : d188546 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130561, d188546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130561, d188546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44149 q ha hb
  have h8 (q : Pattern) (ha : d130562 q = 1) (hb : d188547 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130562, d188547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130562, d188547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130563 q = 1) (hb : d188548 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130563, d188548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130563, d188548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130564 q = 1) (hb : d188549 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130564, d188549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130564, d188549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d130565 q = 1) (hb : d188550 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130565, d188550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130565, d188550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d130566 q = 1) (hb : d188551 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130566, d188551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130566, d188551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro44151 (p : Pattern) (ha : d130600 p = 1) (hb : d188557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130584 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130589 q = 1) (hb : d188552 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130589, d188552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44059 q hb ha
    | true =>
      simp only [d130589, d188552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44052 q hb ha
  have h3 (q : Pattern) (ha : d130590 q = 1) (hb : d188553 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130590, d188553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130590, d188553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130596 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130597 q = 1) (hb : d188554 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130597, d188554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130597, d188554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130598 q = 1) (hb : d188555 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130598, d188555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130598, d188555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130599 q = 1) (hb : d188556 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130599, d188556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130599, d188556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130600 q = 1) (hb : d188557 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130600, d188557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130600, d188557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44152 (p : Pattern) (ha : d130613 p = 1) (hb : d188563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130601 q = 1) (hb : d188558 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130601, d188558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130601, d188558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44151 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130608 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130609 q = 1) (hb : d188559 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130609, d188559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130609, d188559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130610 q = 1) (hb : d188560 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130610, d188560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130610, d188560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130611 q = 1) (hb : d188561 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130611, d188561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130611, d188561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130612 q = 1) (hb : d188562 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130612, d188562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130612, d188562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130613 q = 1) (hb : d188563 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130613, d188563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130613, d188563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44153 (p : Pattern) (ha : d130619 p = 1) (hb : d188569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130614 q = 1) (hb : d188564 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130614, d188564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130614, d188564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44152 q ha hb
  have h2 (q : Pattern) (ha : d130615 q = 1) (hb : d188565 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130615, d188565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130615, d188565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130616 q = 1) (hb : d188566 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130616, d188566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130616, d188566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130617 q = 1) (hb : d188567 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130617, d188567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130617, d188567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130618 q = 1) (hb : d188568 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130618, d188568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130618, d188568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130619 q = 1) (hb : d188569 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130619, d188569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130619, d188569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44154 (p : Pattern) (ha : d130654 p = 1) (hb : d188576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130638 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130643 q = 1) (hb : d188571 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130643, d188571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44075 q hb ha
    | true =>
      simp only [d130643, d188571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44067 q hb ha
  have h3 (q : Pattern) (ha : d130644 q = 1) (hb : d188572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130644, d188572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130644, d188572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130650 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130651 q = 1) (hb : d188573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130651, d188573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130651, d188573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130652 q = 1) (hb : d188574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130652, d188574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130652, d188574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130653 q = 1) (hb : d188575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130653, d188575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130653, d188575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130654 q = 1) (hb : d188576 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130654, d188576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130654, d188576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44155 (p : Pattern) (ha : d130667 p = 1) (hb : d188582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130655 q = 1) (hb : d188577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130655, d188577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130655, d188577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44154 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130662 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130663 q = 1) (hb : d188578 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130663, d188578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130663, d188578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130664 q = 1) (hb : d188579 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130664, d188579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130664, d188579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130665 q = 1) (hb : d188580 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130665, d188580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130665, d188580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130666 q = 1) (hb : d188581 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130666, d188581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130666, d188581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130667 q = 1) (hb : d188582 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130667, d188582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130667, d188582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44156 (p : Pattern) (ha : d130673 p = 1) (hb : d188588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130668 q = 1) (hb : d188583 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130668, d188583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130668, d188583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44155 q ha hb
  have h2 (q : Pattern) (ha : d130669 q = 1) (hb : d188584 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130669, d188584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130669, d188584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130670 q = 1) (hb : d188585 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130670, d188585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130670, d188585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130671 q = 1) (hb : d188586 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130671, d188586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130671, d188586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130672 q = 1) (hb : d188587 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130672, d188587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130672, d188587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130673 q = 1) (hb : d188588 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130673, d188588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130673, d188588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44157 (p : Pattern) (ha : d130694 p = 1) (hb : d188592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9834 q = 1) (hb : d127474 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44086 q ha hb
    | true =>
      simp only [d9834, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44080 q ha hb
  have h2 (q : Pattern) (ha : d20037 q = 1) (hb : d127475 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20037, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20037, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20038 q = 1) (hb : d127476 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20038, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20038, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9851 q = 1) (hb : d127477 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44080 q ha hb
    | true =>
      simp only [d9851, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44088 q ha hb
  have h5 (q : Pattern) (ha : d20039 q = 1) (hb : d127478 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20039, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20039, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20040 q = 1) (hb : d127479 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20040, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20040, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20041 q = 1) (hb : d127480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20041, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20041, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9870 q = 1) (hb : d127494 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, d127494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44080 q ha hb
    | true =>
      simp only [d9870, d127494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44081 q ha hb
  have h9 (q : Pattern) (ha : d20055 q = 1) (hb : d127495 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20055, d127495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20055, d127495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20056 q = 1) (hb : d127496 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20056, d127496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20056, d127496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20057 q = 1) (hb : d127497 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20057, d127497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20057, d127497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d127507 q = 1) (hb : d188591 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127507, d188591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d127507, d188591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h14 (q : Pattern) (ha : d9835 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9836 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h17 (q : Pattern) (ha : d9852 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9853 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9854 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9870 q = 1) (hb : d101391 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23306 q ha hb
  have h21 (q : Pattern) (ha : d9871 q = 1) (hb : d101392 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d9872 q = 1) (hb : d101393 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9873 q = 1) (hb : d101394 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d101404 q = 1) (hb : d129539 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d101404, d129539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d101404, d129539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d130694 q = 1) (hb : d188592 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130694, d188592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d130694, d188592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro44158 (p : Pattern) (ha : d130700 p = 1) (hb : d188598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130695 q = 1) (hb : d188593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130695, d188593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44157 q ha hb
    | true =>
      simp only [d130695, d188593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130696 q = 1) (hb : d188594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130696, d188594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130696, d188594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20060 q = 1) (hb : d130687 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20060, d130687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44082 q ha hb
    | true =>
      simp only [d20060, d130687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20061 q = 1) (hb : d130688 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20061, d130688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20061, d130688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130697 q = 1) (hb : d188595 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130697, d188595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130697, d188595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130698 q = 1) (hb : d188596 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130698, d188596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130698, d188596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130699 q = 1) (hb : d188597 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130699, d188597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130699, d188597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130700 q = 1) (hb : d188598 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130700, d188598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130700, d188598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro44159 (p : Pattern) (ha : d130719 p = 1) (hb : d188604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130693 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130705 q = 1) (hb : d188599 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130705, d188599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44158 q ha hb
    | true =>
      simp only [d130705, d188599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44083 q hb ha
  have h3 (q : Pattern) (ha : d130706 q = 1) (hb : d188600 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130706, d188600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130706, d188600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130715 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130716 q = 1) (hb : d188601 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130716, d188601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130716, d188601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130717 q = 1) (hb : d188602 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130717, d188602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130717, d188602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130718 q = 1) (hb : d188603 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130718, d188603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130718, d188603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130719 q = 1) (hb : d188604 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130719, d188604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130719, d188604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44160 (p : Pattern) (ha : d130732 p = 1) (hb : d188610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130720 q = 1) (hb : d188605 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130720, d188605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130720, d188605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44159 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130727 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130728 q = 1) (hb : d188606 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130728, d188606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130728, d188606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130729 q = 1) (hb : d188607 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130729, d188607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130729, d188607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130730 q = 1) (hb : d188608 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130730, d188608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130730, d188608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130731 q = 1) (hb : d188609 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130731, d188609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130731, d188609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130732 q = 1) (hb : d188610 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130732, d188610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130732, d188610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44161 (p : Pattern) (ha : d130738 p = 1) (hb : d188616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130733 q = 1) (hb : d188611 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130733, d188611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130733, d188611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44160 q ha hb
  have h2 (q : Pattern) (ha : d130734 q = 1) (hb : d188612 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130734, d188612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130734, d188612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130735 q = 1) (hb : d188613 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130735, d188613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130735, d188613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130736 q = 1) (hb : d188614 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130736, d188614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130736, d188614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130737 q = 1) (hb : d188615 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130737, d188615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130737, d188615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130738 q = 1) (hb : d188616 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130738, d188616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130738, d188616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44162 (p : Pattern) (ha : d130760 p = 1) (hb : d188621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10122 q = 1) (hb : d127767 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44105 q ha hb
    | true =>
      simp only [d10122, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44099 q ha hb
  have h2 (q : Pattern) (ha : d20141 q = 1) (hb : d127768 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20141, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20141, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20142 q = 1) (hb : d127769 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20142, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20142, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10142 q = 1) (hb : d127770 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44099 q ha hb
    | true =>
      simp only [d10142, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44107 q ha hb
  have h5 (q : Pattern) (ha : d20143 q = 1) (hb : d127771 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20143, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20143, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20144 q = 1) (hb : d127772 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20144, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20144, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20145 q = 1) (hb : d127773 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20145, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20145, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10164 q = 1) (hb : d127787 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, d127787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44099 q ha hb
    | true =>
      simp only [d10164, d127787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44100 q ha hb
  have h9 (q : Pattern) (ha : d20159 q = 1) (hb : d127788 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20159, d127788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20159, d127788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20160 q = 1) (hb : d127789 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20160, d127789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20160, d127789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20161 q = 1) (hb : d127790 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20161, d127790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20161, d127790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d127800 q = 1) (hb : d188620 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127800, d188620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d127800, d188620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h14 (q : Pattern) (ha : d10123 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10124 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h17 (q : Pattern) (ha : d10143 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10144 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10145 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10164 q = 1) (hb : d101591 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23334 q ha hb
  have h21 (q : Pattern) (ha : d10165 q = 1) (hb : d101592 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10166 q = 1) (hb : d101593 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10167 q = 1) (hb : d101594 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d101604 q = 1) (hb : d129568 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d101604, d129568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d101604, d129568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d130760 q = 1) (hb : d188621 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130760, d188621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d130760, d188621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro44163 (p : Pattern) (ha : d130766 p = 1) (hb : d188627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130761 q = 1) (hb : d188622 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130761, d188622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44162 q ha hb
    | true =>
      simp only [d130761, d188622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130762 q = 1) (hb : d188623 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130762, d188623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130762, d188623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20164 q = 1) (hb : d130753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20164, d130753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44101 q ha hb
    | true =>
      simp only [d20164, d130753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20165 q = 1) (hb : d130754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20165, d130754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20165, d130754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130763 q = 1) (hb : d188624 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130763, d188624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130763, d188624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130764 q = 1) (hb : d188625 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130764, d188625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130764, d188625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130765 q = 1) (hb : d188626 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130765, d188626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130765, d188626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130766 q = 1) (hb : d188627 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130766, d188627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130766, d188627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro44164 (p : Pattern) (ha : d130785 p = 1) (hb : d188633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130759 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130771 q = 1) (hb : d188628 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130771, d188628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44163 q ha hb
    | true =>
      simp only [d130771, d188628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44102 q hb ha
  have h3 (q : Pattern) (ha : d130772 q = 1) (hb : d188629 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130772, d188629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130772, d188629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130781 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130782 q = 1) (hb : d188630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130782, d188630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130782, d188630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130783 q = 1) (hb : d188631 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130783, d188631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130783, d188631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130784 q = 1) (hb : d188632 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130784, d188632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130784, d188632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130785 q = 1) (hb : d188633 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130785, d188633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130785, d188633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44165 (p : Pattern) (ha : d130798 p = 1) (hb : d188639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130786 q = 1) (hb : d188634 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130786, d188634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130786, d188634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44164 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130793 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130794 q = 1) (hb : d188635 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130794, d188635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130794, d188635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130795 q = 1) (hb : d188636 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130795, d188636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130795, d188636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130796 q = 1) (hb : d188637 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130796, d188637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130796, d188637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130797 q = 1) (hb : d188638 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130797, d188638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130797, d188638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130798 q = 1) (hb : d188639 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130798, d188639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130798, d188639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44166 (p : Pattern) (ha : d130804 p = 1) (hb : d188645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130799 q = 1) (hb : d188640 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130799, d188640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130799, d188640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44165 q ha hb
  have h2 (q : Pattern) (ha : d130800 q = 1) (hb : d188641 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130800, d188641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130800, d188641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130801 q = 1) (hb : d188642 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130801, d188642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130801, d188642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130802 q = 1) (hb : d188643 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130802, d188643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130802, d188643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130803 q = 1) (hb : d188644 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130803, d188644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130803, d188644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130804 q = 1) (hb : d188645 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130804, d188645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130804, d188645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44167 (p : Pattern) (ha : d130827 p = 1) (hb : d188651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10398 q = 1) (hb : d128059 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44124 q ha hb
    | true =>
      simp only [d10398, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44118 q ha hb
  have h2 (q : Pattern) (ha : d20246 q = 1) (hb : d128060 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20246, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20246, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20247 q = 1) (hb : d128061 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20247, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20247, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10419 q = 1) (hb : d128062 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44118 q ha hb
    | true =>
      simp only [d10419, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44126 q ha hb
  have h5 (q : Pattern) (ha : d20248 q = 1) (hb : d128063 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20248, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20248, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20249 q = 1) (hb : d128064 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20249, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20249, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20250 q = 1) (hb : d128065 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20250, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20250, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10441 q = 1) (hb : d128079 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, d128079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44118 q ha hb
    | true =>
      simp only [d10441, d128079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44119 q ha hb
  have h9 (q : Pattern) (ha : d20264 q = 1) (hb : d128080 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20264, d128080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20264, d128080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20265 q = 1) (hb : d128081 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20265, d128081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20265, d128081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20266 q = 1) (hb : d128082 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20266, d128082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20266, d128082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128092 q = 1) (hb : d188650 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128092, d188650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d128092, d188650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h14 (q : Pattern) (ha : d10399 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10400 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h17 (q : Pattern) (ha : d10420 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10421 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10422 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10441 q = 1) (hb : d101762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23362 q ha hb
  have h21 (q : Pattern) (ha : d10442 q = 1) (hb : d101763 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10443 q = 1) (hb : d101764 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10444 q = 1) (hb : d101765 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d101775 q = 1) (hb : d129598 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d101775, d129598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d101775, d129598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d130827 q = 1) (hb : d188651 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130827, d188651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d130827, d188651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro44168 (p : Pattern) (ha : d130833 p = 1) (hb : d188657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130828 q = 1) (hb : d188652 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130828, d188652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44167 q ha hb
    | true =>
      simp only [d130828, d188652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130829 q = 1) (hb : d188653 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130829, d188653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130829, d188653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20269 q = 1) (hb : d130820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20269, d130820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44120 q ha hb
    | true =>
      simp only [d20269, d130820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20270 q = 1) (hb : d130821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20270, d130821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20270, d130821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130830 q = 1) (hb : d188654 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130830, d188654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130830, d188654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130831 q = 1) (hb : d188655 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130831, d188655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130831, d188655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130832 q = 1) (hb : d188656 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130832, d188656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130832, d188656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130833 q = 1) (hb : d188657 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130833, d188657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130833, d188657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro44169 (p : Pattern) (ha : d130852 p = 1) (hb : d188663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130826 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130838 q = 1) (hb : d188658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130838, d188658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44168 q ha hb
    | true =>
      simp only [d130838, d188658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44121 q hb ha
  have h3 (q : Pattern) (ha : d130839 q = 1) (hb : d188659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130839, d188659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130839, d188659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130848 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130849 q = 1) (hb : d188660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130849, d188660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130849, d188660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130850 q = 1) (hb : d188661 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130850, d188661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130850, d188661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130851 q = 1) (hb : d188662 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130851, d188662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130851, d188662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130852 q = 1) (hb : d188663 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130852, d188663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130852, d188663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44170 (p : Pattern) (ha : d130865 p = 1) (hb : d188669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130853 q = 1) (hb : d188664 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130853, d188664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130853, d188664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44169 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130860 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130861 q = 1) (hb : d188665 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130861, d188665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130861, d188665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130862 q = 1) (hb : d188666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130862, d188666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130862, d188666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130863 q = 1) (hb : d188667 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130863, d188667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130863, d188667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130864 q = 1) (hb : d188668 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130864, d188668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130864, d188668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130865 q = 1) (hb : d188669 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130865, d188669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130865, d188669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44171 (p : Pattern) (ha : d130871 p = 1) (hb : d188675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130866 q = 1) (hb : d188670 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130866, d188670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130866, d188670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44170 q ha hb
  have h2 (q : Pattern) (ha : d130867 q = 1) (hb : d188671 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130867, d188671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130867, d188671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130868 q = 1) (hb : d188672 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130868, d188672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130868, d188672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130869 q = 1) (hb : d188673 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130869, d188673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130869, d188673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130870 q = 1) (hb : d188674 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130870, d188674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130870, d188674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130871 q = 1) (hb : d188675 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130871, d188675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130871, d188675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44172 (p : Pattern) (ha : d130877 p = 1) (hb : d188681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d130620 q = 1) (hb : d188570 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130620, d188570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44150 q ha hb
    | true =>
      simp only [d130620, d188570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44153 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130674 q = 1) (hb : d188589 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130674, d188589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130674, d188589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44156 q ha hb
  have h3 (q : Pattern) (ha : d130675 q = 1) (hb : d188590 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130675, d188590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130675, d188590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130739 q = 1) (hb : d188617 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130739, d188617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130739, d188617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44161 q ha hb
  have h5 (q : Pattern) (ha : d130740 q = 1) (hb : d188618 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130740, d188618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130740, d188618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130741 q = 1) (hb : d188619 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130741, d188619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130741, d188619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130805 q = 1) (hb : d188646 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130805, d188646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130805, d188646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44166 q ha hb
  have h8 (q : Pattern) (ha : d130806 q = 1) (hb : d188647 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130806, d188647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130806, d188647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130807 q = 1) (hb : d188648 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130807, d188648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130807, d188648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130808 q = 1) (hb : d188649 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130808, d188649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130808, d188649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d130872 q = 1) (hb : d188676 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130872, d188676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130872, d188676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44171 q ha hb
  have h12 (q : Pattern) (ha : d130873 q = 1) (hb : d188677 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130873, d188677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130873, d188677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d130874 q = 1) (hb : d188678 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130874, d188678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130874, d188678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d130875 q = 1) (hb : d188679 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130875, d188679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130875, d188679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d130876 q = 1) (hb : d188680 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d130876, d188680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d130876, d188680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d130877 q = 1) (hb : d188681 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d130877, d188681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d130877, d188681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro44173 (p : Pattern) (ha : d130883 p = 1) (hb : d188687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130878 q = 1) (hb : d188682 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d130878, d188682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44172 q ha hb
    | true =>
      simp only [d130878, d188682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130879 q = 1) (hb : d188683 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d130879, d188683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130879, d188683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130880 q = 1) (hb : d188684 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d130880, d188684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130880, d188684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130881 q = 1) (hb : d188685 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d130881, d188685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130881, d188685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130882 q = 1) (hb : d188686 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d130882, d188686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130882, d188686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130883 q = 1) (hb : d188687 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d130883, d188687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130883, d188687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44174 (p : Pattern) (ha : d130889 p = 1) (hb : d188693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130884 q = 1) (hb : d188688 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d130884, d188688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44173 q ha hb
    | true =>
      simp only [d130884, d188688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130885 q = 1) (hb : d188689 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d130885, d188689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130885, d188689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130886 q = 1) (hb : d188690 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d130886, d188690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130886, d188690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130887 q = 1) (hb : d188691 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d130887, d188691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130887, d188691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130888 q = 1) (hb : d188692 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d130888, d188692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130888, d188692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130889 q = 1) (hb : d188693 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d130889, d188693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130889, d188693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44175 (p : Pattern) (ha : d130895 p = 1) (hb : d188699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130890 q = 1) (hb : d188694 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d130890, d188694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44174 q ha hb
    | true =>
      simp only [d130890, d188694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130891 q = 1) (hb : d188695 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d130891, d188695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130891, d188695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130892 q = 1) (hb : d188696 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d130892, d188696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130892, d188696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130893 q = 1) (hb : d188697 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d130893, d188697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130893, d188697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130894 q = 1) (hb : d188698 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d130894, d188698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130894, d188698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130895 q = 1) (hb : d188699 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d130895, d188699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130895, d188699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44176 (p : Pattern) (ha : d130901 p = 1) (hb : d188705 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130896 q = 1) (hb : d188700 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d130896, d188700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44175 q ha hb
    | true =>
      simp only [d130896, d188700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130897 q = 1) (hb : d188701 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d130897, d188701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130897, d188701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130898 q = 1) (hb : d188702 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d130898, d188702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130898, d188702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130899 q = 1) (hb : d188703 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d130899, d188703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130899, d188703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130900 q = 1) (hb : d188704 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d130900, d188704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130900, d188704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130901 q = 1) (hb : d188705 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d130901, d188705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130901, d188705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44177 (p : Pattern) (ha : d130907 p = 1) (hb : d188711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130902 q = 1) (hb : d188706 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d130902, d188706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44176 q ha hb
    | true =>
      simp only [d130902, d188706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130903 q = 1) (hb : d188707 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d130903, d188707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130903, d188707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130904 q = 1) (hb : d188708 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d130904, d188708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130904, d188708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130905 q = 1) (hb : d188709 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d130905, d188709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130905, d188709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130906 q = 1) (hb : d188710 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d130906, d188710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130906, d188710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130907 q = 1) (hb : d188711 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d130907, d188711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130907, d188711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44178 (p : Pattern) (ha : d130913 p = 1) (hb : d188717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130908 q = 1) (hb : d188712 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d130908, d188712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44177 q ha hb
    | true =>
      simp only [d130908, d188712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130909 q = 1) (hb : d188713 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d130909, d188713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130909, d188713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130910 q = 1) (hb : d188714 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d130910, d188714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130910, d188714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130911 q = 1) (hb : d188715 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d130911, d188715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130911, d188715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130912 q = 1) (hb : d188716 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d130912, d188716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130912, d188716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130913 q = 1) (hb : d188717 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d130913, d188717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130913, d188717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44179 (p : Pattern) (ha : d130919 p = 1) (hb : d188723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130914 q = 1) (hb : d188718 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d130914, d188718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44178 q ha hb
    | true =>
      simp only [d130914, d188718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130915 q = 1) (hb : d188719 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d130915, d188719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130915, d188719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130916 q = 1) (hb : d188720 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d130916, d188720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130916, d188720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130917 q = 1) (hb : d188721 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d130917, d188721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130917, d188721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130918 q = 1) (hb : d188722 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d130918, d188722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130918, d188722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130919 q = 1) (hb : d188723 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d130919, d188723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130919, d188723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44180 (p : Pattern) (ha : d19845 p = 1) (hb : d130924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20420 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19749 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19841 q = 1) (hb : d130920 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19841, d130920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19841, d130920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20398 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d19842 q = 1) (hb : d130921 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19842, d130921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19842, d130921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19843 q = 1) (hb : d130922 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19843, d130922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19843, d130922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19844 q = 1) (hb : d130923 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19844, d130923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19844, d130923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19845 q = 1) (hb : d130924 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19845, d130924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19845, d130924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44181 (p : Pattern) (ha : d130930 p = 1) (hb : d188529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19846 q = 1) (hb : d130925 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19846, d130925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19846, d130925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44180 q ha hb
  have h2 (q : Pattern) (ha : d130926 q = 1) (hb : d188525 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130926, d188525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130926, d188525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d130927 q = 1) (hb : d188526 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130927, d188526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130927, d188526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d130928 q = 1) (hb : d188527 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130928, d188527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130928, d188527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130929 q = 1) (hb : d188528 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130929, d188528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130929, d188528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130930 q = 1) (hb : d188529 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130930, d188529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130930, d188529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44182 (p : Pattern) (ha : d130940 p = 1) (hb : d188539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20452 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19776 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130936 q = 1) (hb : d188535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130936, d188535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130936, d188535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20467 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130937 q = 1) (hb : d188536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130937, d188536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130937, d188536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130938 q = 1) (hb : d188537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130938, d188537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130938, d188537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130939 q = 1) (hb : d188538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130939, d188538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130939, d188538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130940 q = 1) (hb : d188539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130940, d188539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130940, d188539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44183 (p : Pattern) (ha : d130946 p = 1) (hb : d188545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130941 q = 1) (hb : d188540 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130941, d188540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130941, d188540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44182 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20478 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130942 q = 1) (hb : d188541 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130942, d188541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130942, d188541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130943 q = 1) (hb : d188542 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130943, d188542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130943, d188542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130944 q = 1) (hb : d188543 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130944, d188543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130944, d188543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130945 q = 1) (hb : d188544 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130945, d188544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130945, d188544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130946 q = 1) (hb : d188545 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130946, d188545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130946, d188545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44184 (p : Pattern) (ha : d130952 p = 1) (hb : d188551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d20412 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130931 q = 1) (hb : d188530 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130931, d188530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130931, d188530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44181 q ha hb
  have h3 (q : Pattern) (ha : d130932 q = 1) (hb : d188531 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130932, d188531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130932, d188531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130933 q = 1) (hb : d188532 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130933, d188532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130933, d188532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130934 q = 1) (hb : d188533 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130934, d188533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130934, d188533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130935 q = 1) (hb : d188534 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130935, d188534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130935, d188534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130947 q = 1) (hb : d188546 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130947, d188546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130947, d188546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44183 q ha hb
  have h8 (q : Pattern) (ha : d130948 q = 1) (hb : d188547 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130948, d188547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130948, d188547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130949 q = 1) (hb : d188548 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130949, d188548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130949, d188548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130950 q = 1) (hb : d188549 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130950, d188549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130950, d188549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d130951 q = 1) (hb : d188550 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130951, d188550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130951, d188550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d130952 q = 1) (hb : d188551 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130952, d188551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130952, d188551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro44185 (p : Pattern) (ha : d130957 p = 1) (hb : d188557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20507 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d188552 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130953 q = 1) (hb : d188553 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130953, d188553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130953, d188553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20529 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130954 q = 1) (hb : d188554 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130954, d188554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130954, d188554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130955 q = 1) (hb : d188555 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130955, d188555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130955, d188555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130956 q = 1) (hb : d188556 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130956, d188556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130956, d188556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130957 q = 1) (hb : d188557 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130957, d188557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130957, d188557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44186 (p : Pattern) (ha : d130963 p = 1) (hb : d188563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130958 q = 1) (hb : d188558 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130958, d188558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130958, d188558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44185 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20545 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130959 q = 1) (hb : d188559 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130959, d188559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130959, d188559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130960 q = 1) (hb : d188560 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130960, d188560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130960, d188560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130961 q = 1) (hb : d188561 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130961, d188561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130961, d188561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130962 q = 1) (hb : d188562 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130962, d188562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130962, d188562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130963 q = 1) (hb : d188563 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130963, d188563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130963, d188563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44187 (p : Pattern) (ha : d130969 p = 1) (hb : d188569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130964 q = 1) (hb : d188564 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130964, d188564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130964, d188564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44186 q ha hb
  have h2 (q : Pattern) (ha : d130965 q = 1) (hb : d188565 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130965, d188565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130965, d188565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130966 q = 1) (hb : d188566 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130966, d188566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130966, d188566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130967 q = 1) (hb : d188567 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130967, d188567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130967, d188567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130968 q = 1) (hb : d188568 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130968, d188568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130968, d188568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130969 q = 1) (hb : d188569 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130969, d188569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130969, d188569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44188 (p : Pattern) (ha : d130975 p = 1) (hb : d188576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20575 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d188571 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130971 q = 1) (hb : d188572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130971, d188572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130971, d188572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20597 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130972 q = 1) (hb : d188573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130972, d188573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130972, d188573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130973 q = 1) (hb : d188574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130973, d188574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130973, d188574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130974 q = 1) (hb : d188575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130974, d188575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130974, d188575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130975 q = 1) (hb : d188576 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130975, d188576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130975, d188576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44189 (p : Pattern) (ha : d130981 p = 1) (hb : d188582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130976 q = 1) (hb : d188577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130976, d188577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130976, d188577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44188 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20613 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130977 q = 1) (hb : d188578 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130977, d188578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130977, d188578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130978 q = 1) (hb : d188579 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130978, d188579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130978, d188579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130979 q = 1) (hb : d188580 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130979, d188580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130979, d188580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130980 q = 1) (hb : d188581 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130980, d188581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130980, d188581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130981 q = 1) (hb : d188582 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130981, d188582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130981, d188582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44190 (p : Pattern) (ha : d130987 p = 1) (hb : d188588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130982 q = 1) (hb : d188583 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130982, d188583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130982, d188583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44189 q ha hb
  have h2 (q : Pattern) (ha : d130983 q = 1) (hb : d188584 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130983, d188584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130983, d188584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130984 q = 1) (hb : d188585 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130984, d188585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130984, d188585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130985 q = 1) (hb : d188586 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130985, d188586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130985, d188586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130986 q = 1) (hb : d188587 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130986, d188587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130986, d188587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130987 q = 1) (hb : d188588 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130987, d188588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130987, d188588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44191 (p : Pattern) (ha : d130994 p = 1) (hb : d188604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20644 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d188599 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130990 q = 1) (hb : d188600 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130990, d188600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130990, d188600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20669 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130991 q = 1) (hb : d188601 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130991, d188601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130991, d188601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130992 q = 1) (hb : d188602 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130992, d188602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130992, d188602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130993 q = 1) (hb : d188603 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130993, d188603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130993, d188603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130994 q = 1) (hb : d188604 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130994, d188604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130994, d188604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44192 (p : Pattern) (ha : d131000 p = 1) (hb : d188610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130995 q = 1) (hb : d188605 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130995, d188605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130995, d188605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44191 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20685 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130996 q = 1) (hb : d188606 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130996, d188606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130996, d188606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130997 q = 1) (hb : d188607 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130997, d188607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130997, d188607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130998 q = 1) (hb : d188608 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130998, d188608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130998, d188608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130999 q = 1) (hb : d188609 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130999, d188609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130999, d188609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d131000 q = 1) (hb : d188610 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131000, d188610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131000, d188610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44193 (p : Pattern) (ha : d131006 p = 1) (hb : d188616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131001 q = 1) (hb : d188611 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131001, d188611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131001, d188611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44192 q ha hb
  have h2 (q : Pattern) (ha : d131002 q = 1) (hb : d188612 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131002, d188612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131002, d188612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131003 q = 1) (hb : d188613 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131003, d188613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131003, d188613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131004 q = 1) (hb : d188614 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131004, d188614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131004, d188614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131005 q = 1) (hb : d188615 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131005, d188615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131005, d188615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131006 q = 1) (hb : d188616 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131006, d188616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131006, d188616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44194 (p : Pattern) (ha : d131014 p = 1) (hb : d188633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20717 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d188628 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131010 q = 1) (hb : d188629 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131010, d188629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131010, d188629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20742 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131011 q = 1) (hb : d188630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131011, d188630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131011, d188630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131012 q = 1) (hb : d188631 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131012, d188631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131012, d188631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131013 q = 1) (hb : d188632 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131013, d188632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131013, d188632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131014 q = 1) (hb : d188633 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131014, d188633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131014, d188633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44195 (p : Pattern) (ha : d131020 p = 1) (hb : d188639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131015 q = 1) (hb : d188634 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131015, d188634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131015, d188634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44194 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20758 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131016 q = 1) (hb : d188635 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131016, d188635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131016, d188635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131017 q = 1) (hb : d188636 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131017, d188636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131017, d188636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131018 q = 1) (hb : d188637 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131018, d188637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131018, d188637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131019 q = 1) (hb : d188638 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131019, d188638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131019, d188638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d131020 q = 1) (hb : d188639 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131020, d188639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131020, d188639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44196 (p : Pattern) (ha : d131026 p = 1) (hb : d188645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131021 q = 1) (hb : d188640 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131021, d188640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131021, d188640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44195 q ha hb
  have h2 (q : Pattern) (ha : d131022 q = 1) (hb : d188641 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131022, d188641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131022, d188641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131023 q = 1) (hb : d188642 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131023, d188642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131023, d188642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131024 q = 1) (hb : d188643 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131024, d188643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131024, d188643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131025 q = 1) (hb : d188644 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131025, d188644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131025, d188644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131026 q = 1) (hb : d188645 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131026, d188645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131026, d188645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44197 (p : Pattern) (ha : d131035 p = 1) (hb : d188663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20791 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d188658 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131031 q = 1) (hb : d188659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131031, d188659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131031, d188659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20816 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131032 q = 1) (hb : d188660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131032, d188660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131032, d188660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131033 q = 1) (hb : d188661 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131033, d188661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131033, d188661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131034 q = 1) (hb : d188662 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131034, d188662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131034, d188662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131035 q = 1) (hb : d188663 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131035, d188663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131035, d188663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44198 (p : Pattern) (ha : d131041 p = 1) (hb : d188669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131036 q = 1) (hb : d188664 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131036, d188664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131036, d188664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44197 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20832 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131037 q = 1) (hb : d188665 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131037, d188665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131037, d188665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131038 q = 1) (hb : d188666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131038, d188666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131038, d188666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131039 q = 1) (hb : d188667 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131039, d188667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131039, d188667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131040 q = 1) (hb : d188668 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131040, d188668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131040, d188668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d131041 q = 1) (hb : d188669 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131041, d188669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131041, d188669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44199 (p : Pattern) (ha : d131047 p = 1) (hb : d188675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131042 q = 1) (hb : d188670 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131042, d188670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131042, d188670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44198 q ha hb
  have h2 (q : Pattern) (ha : d131043 q = 1) (hb : d188671 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131043, d188671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131043, d188671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131044 q = 1) (hb : d188672 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131044, d188672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131044, d188672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131045 q = 1) (hb : d188673 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131045, d188673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131045, d188673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131046 q = 1) (hb : d188674 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131046, d188674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131046, d188674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131047 q = 1) (hb : d188675 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131047, d188675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131047, d188675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44200 (p : Pattern) (ha : d131053 p = 1) (hb : d188681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d130970 q = 1) (hb : d188570 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130970, d188570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44184 q ha hb
    | true =>
      simp only [d130970, d188570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44187 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130988 q = 1) (hb : d188589 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130988, d188589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130988, d188589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44190 q ha hb
  have h3 (q : Pattern) (ha : d130989 q = 1) (hb : d188590 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130989, d188590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130989, d188590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131007 q = 1) (hb : d188617 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131007, d188617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131007, d188617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44193 q ha hb
  have h5 (q : Pattern) (ha : d131008 q = 1) (hb : d188618 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131008, d188618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131008, d188618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131009 q = 1) (hb : d188619 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131009, d188619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131009, d188619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131027 q = 1) (hb : d188646 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131027, d188646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131027, d188646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44196 q ha hb
  have h8 (q : Pattern) (ha : d131028 q = 1) (hb : d188647 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131028, d188647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131028, d188647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131029 q = 1) (hb : d188648 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131029, d188648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131029, d188648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131030 q = 1) (hb : d188649 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131030, d188649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131030, d188649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131048 q = 1) (hb : d188676 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131048, d188676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131048, d188676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44199 q ha hb
  have h12 (q : Pattern) (ha : d131049 q = 1) (hb : d188677 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131049, d188677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131049, d188677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d131050 q = 1) (hb : d188678 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131050, d188678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131050, d188678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131051 q = 1) (hb : d188679 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131051, d188679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131051, d188679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d131052 q = 1) (hb : d188680 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d131052, d188680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131052, d188680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d131053 q = 1) (hb : d188681 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d131053, d188681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131053, d188681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro44201 (p : Pattern) (ha : d131059 p = 1) (hb : d188687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131054 q = 1) (hb : d188682 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d131054, d188682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44200 q ha hb
    | true =>
      simp only [d131054, d188682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131055 q = 1) (hb : d188683 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d131055, d188683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131055, d188683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131056 q = 1) (hb : d188684 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d131056, d188684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131056, d188684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131057 q = 1) (hb : d188685 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d131057, d188685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131057, d188685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131058 q = 1) (hb : d188686 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d131058, d188686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131058, d188686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131059 q = 1) (hb : d188687 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d131059, d188687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131059, d188687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44202 (p : Pattern) (ha : d131065 p = 1) (hb : d188693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131060 q = 1) (hb : d188688 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d131060, d188688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44201 q ha hb
    | true =>
      simp only [d131060, d188688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131061 q = 1) (hb : d188689 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d131061, d188689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131061, d188689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131062 q = 1) (hb : d188690 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d131062, d188690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131062, d188690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131063 q = 1) (hb : d188691 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d131063, d188691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131063, d188691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131064 q = 1) (hb : d188692 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d131064, d188692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131064, d188692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131065 q = 1) (hb : d188693 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d131065, d188693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131065, d188693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44203 (p : Pattern) (ha : d131071 p = 1) (hb : d188699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131066 q = 1) (hb : d188694 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d131066, d188694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44202 q ha hb
    | true =>
      simp only [d131066, d188694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131067 q = 1) (hb : d188695 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d131067, d188695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131067, d188695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131068 q = 1) (hb : d188696 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d131068, d188696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131068, d188696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131069 q = 1) (hb : d188697 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d131069, d188697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131069, d188697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131070 q = 1) (hb : d188698 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d131070, d188698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131070, d188698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131071 q = 1) (hb : d188699 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d131071, d188699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131071, d188699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44204 (p : Pattern) (ha : d131077 p = 1) (hb : d188705 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131072 q = 1) (hb : d188700 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d131072, d188700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44203 q ha hb
    | true =>
      simp only [d131072, d188700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131073 q = 1) (hb : d188701 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d131073, d188701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131073, d188701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131074 q = 1) (hb : d188702 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d131074, d188702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131074, d188702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131075 q = 1) (hb : d188703 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d131075, d188703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131075, d188703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131076 q = 1) (hb : d188704 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d131076, d188704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131076, d188704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131077 q = 1) (hb : d188705 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d131077, d188705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131077, d188705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44205 (p : Pattern) (ha : d131083 p = 1) (hb : d188711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131078 q = 1) (hb : d188706 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d131078, d188706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44204 q ha hb
    | true =>
      simp only [d131078, d188706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131079 q = 1) (hb : d188707 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d131079, d188707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131079, d188707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131080 q = 1) (hb : d188708 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d131080, d188708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131080, d188708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131081 q = 1) (hb : d188709 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d131081, d188709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131081, d188709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131082 q = 1) (hb : d188710 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d131082, d188710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131082, d188710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131083 q = 1) (hb : d188711 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d131083, d188711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131083, d188711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44206 (p : Pattern) (ha : d131089 p = 1) (hb : d188717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131084 q = 1) (hb : d188712 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d131084, d188712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44205 q ha hb
    | true =>
      simp only [d131084, d188712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131085 q = 1) (hb : d188713 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d131085, d188713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131085, d188713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131086 q = 1) (hb : d188714 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d131086, d188714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131086, d188714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131087 q = 1) (hb : d188715 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d131087, d188715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131087, d188715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131088 q = 1) (hb : d188716 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d131088, d188716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131088, d188716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131089 q = 1) (hb : d188717 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d131089, d188717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131089, d188717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44207 (p : Pattern) (ha : d131095 p = 1) (hb : d188723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131090 q = 1) (hb : d188718 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d131090, d188718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44206 q ha hb
    | true =>
      simp only [d131090, d188718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131091 q = 1) (hb : d188719 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d131091, d188719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131091, d188719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131092 q = 1) (hb : d188720 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d131092, d188720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131092, d188720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131093 q = 1) (hb : d188721 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d131093, d188721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131093, d188721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131094 q = 1) (hb : d188722 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d131094, d188722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131094, d188722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131095 q = 1) (hb : d188723 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d131095, d188723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131095, d188723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44208 (p : Pattern) (ha : d130386 p = 1) (hb : d190594 p = 1) : d130386 p = 1 := by
  have h0 (q : Pattern) (ha : d130386 q = 1) (hb : d190594 q = 1) : d130386 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro44209 (p : Pattern) (ha : d188723 p = 1) (hb : d190594 p = 1) : d188723 p = 1 := by
  have h0 (q : Pattern) (ha : d188723 q = 1) (hb : d190594 q = 1) : d188723 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro44210 (p : Pattern) (ha : d19742 p = 1) (hb : d131098 p = 1) : d187879 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9297 q = 1) (hb : d131098 q = 1) : d31 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23756 q ha hb
    | true =>
      simp only [d9297, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19738 q = 1) (hb : d131098 q = 1) : d32 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19738, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19738, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19739 q = 1) (hb : d131098 q = 1) : d33 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19739, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19739, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19740 q = 1) (hb : d131098 q = 1) : d34 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19740, d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19740, d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19741 q = 1) (hb : d131098 q = 1) : d35 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19741, d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19741, d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9298 q = 1) (hb : d131098 q = 1) : d18544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d18544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9298, d18544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9299 q = 1) (hb : d131098 q = 1) : d18545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d18545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9299, d18545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9300 q = 1) (hb : d131098 q = 1) : d18546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9300, d18546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9300, d18546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9301 q = 1) (hb : d131098 q = 1) : d18547 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9301, d18547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9301, d18547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19742 q = 1) (hb : d131098 q = 1) : d187879 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19742, d187879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19742, d187879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro44211 (p : Pattern) (ha : d19748 p = 1) (hb : d131098 p = 1) : d187885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19743 q = 1) (hb : d131098 q = 1) : d187880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19743, d187880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44210 q ha hb
    | true =>
      simp only [d19743, d187880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19744 q = 1) (hb : d131098 q = 1) : d187881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19744, d187881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19744, d187881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19745 q = 1) (hb : d131098 q = 1) : d187882 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19745, d187882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19745, d187882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19746 q = 1) (hb : d131098 q = 1) : d187883 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19746, d187883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19746, d187883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19747 q = 1) (hb : d131098 q = 1) : d187884 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19747, d187884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19747, d187884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19748 q = 1) (hb : d131098 q = 1) : d187885 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19748, d187885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19748, d187885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44212 (p : Pattern) (ha : d19754 p = 1) (hb : d131098 p = 1) : d187891 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19749 q = 1) (hb : d131098 q = 1) : d187886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19749, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44211 q ha hb
    | true =>
      simp only [d19749, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19750 q = 1) (hb : d131098 q = 1) : d187887 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19750, d187887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19750, d187887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19751 q = 1) (hb : d131098 q = 1) : d187888 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19751, d187888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19751, d187888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19752 q = 1) (hb : d131098 q = 1) : d187889 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19752, d187889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19752, d187889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19753 q = 1) (hb : d131098 q = 1) : d187890 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19753, d187890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19753, d187890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19754 q = 1) (hb : d131098 q = 1) : d187891 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19754, d187891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19754, d187891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44213 (p : Pattern) (ha : d19760 p = 1) (hb : d131098 p = 1) : d187897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19755 q = 1) (hb : d131098 q = 1) : d187892 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19755, d187892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19755, d187892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44212 q ha hb
  have h2 (q : Pattern) (ha : d19756 q = 1) (hb : d131098 q = 1) : d187893 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d19756, d187893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19756, d187893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19757 q = 1) (hb : d131098 q = 1) : d187894 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d19757, d187894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19757, d187894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19758 q = 1) (hb : d131098 q = 1) : d187895 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d19758, d187895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19758, d187895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19759 q = 1) (hb : d131098 q = 1) : d187896 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d19759, d187896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19759, d187896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19760 q = 1) (hb : d131098 q = 1) : d187897 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d19760, d187897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19760, d187897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44214 (p : Pattern) (ha : d19769 p = 1) (hb : d131098 p = 1) : d187902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9330 q = 1) (hb : d131098 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23761 q ha hb
    | true =>
      simp only [d9330, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23756 q ha hb
  have h2 (q : Pattern) (ha : d19765 q = 1) (hb : d131098 q = 1) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19765, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19766 q = 1) (hb : d131098 q = 1) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9297 q = 1) (hb : d131098 q = 1) : d31 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23756 q ha hb
    | true =>
      simp only [d9297, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19738 q = 1) (hb : d131098 q = 1) : d32 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19738, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19738, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19739 q = 1) (hb : d131098 q = 1) : d33 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19739, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19739, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19767 q = 1) (hb : d131098 q = 1) : d148 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19767, d148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19767, d148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19740 q = 1) (hb : d131098 q = 1) : d34 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19740, d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19740, d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19768 q = 1) (hb : d131098 q = 1) : d149 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19768, d149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19768, d149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9331 q = 1) (hb : d131098 q = 1) : d18581 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9331, d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9332 q = 1) (hb : d131098 q = 1) : d18582 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9298 q = 1) (hb : d131098 q = 1) : d18544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d18544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9298, d18544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9299 q = 1) (hb : d131098 q = 1) : d18545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d18545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9299, d18545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9333 q = 1) (hb : d131098 q = 1) : d18583 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9333, d18583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9333, d18583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9300 q = 1) (hb : d131098 q = 1) : d18546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9300, d18546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9300, d18546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d9334 q = 1) (hb : d131098 q = 1) : d18584 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9334, d18584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9334, d18584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19769 q = 1) (hb : d131098 q = 1) : d187902 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19769, d187902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19769, d187902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro44215 (p : Pattern) (ha : d19775 p = 1) (hb : d131098 p = 1) : d187908 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19770 q = 1) (hb : d131098 q = 1) : d187903 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19770, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44214 q ha hb
    | true =>
      simp only [d19770, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19771 q = 1) (hb : d131098 q = 1) : d187904 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19771, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19771, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19743 q = 1) (hb : d131098 q = 1) : d187880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19743, d187880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44210 q ha hb
    | true =>
      simp only [d19743, d187880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19744 q = 1) (hb : d131098 q = 1) : d187881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19744, d187881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19744, d187881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19772 q = 1) (hb : d131098 q = 1) : d187905 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19772, d187905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19772, d187905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19773 q = 1) (hb : d131098 q = 1) : d187906 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19773, d187906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19773, d187906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19774 q = 1) (hb : d131098 q = 1) : d187907 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19774, d187907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19774, d187907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19775 q = 1) (hb : d131098 q = 1) : d187908 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19775, d187908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19775, d187908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44216 (p : Pattern) (ha : d130215 p = 1) (hb : d131098 p = 1) : d187914 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19776 q = 1) (hb : d131098 q = 1) : d187909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19776, d187909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44215 q ha hb
    | true =>
      simp only [d19776, d187909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44211 q ha hb
  have h2 (q : Pattern) (ha : d130211 q = 1) (hb : d131098 q = 1) : d187910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130211, d187910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130211, d187910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19749 q = 1) (hb : d131098 q = 1) : d187886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19749, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44211 q ha hb
    | true =>
      simp only [d19749, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19750 q = 1) (hb : d131098 q = 1) : d187887 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19750, d187887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19750, d187887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130212 q = 1) (hb : d131098 q = 1) : d187911 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130212, d187911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130212, d187911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130213 q = 1) (hb : d131098 q = 1) : d187912 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130213, d187912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130213, d187912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130214 q = 1) (hb : d131098 q = 1) : d187913 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130214, d187913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130214, d187913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130215 q = 1) (hb : d131098 q = 1) : d187914 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130215, d187914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130215, d187914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44217 (p : Pattern) (ha : d130221 p = 1) (hb : d131098 p = 1) : d187920 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130216 q = 1) (hb : d131098 q = 1) : d187915 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130216, d187915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130216, d187915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44216 q ha hb
  have h2 (q : Pattern) (ha : d130217 q = 1) (hb : d131098 q = 1) : d187916 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130217, d187916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130217, d187916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d130218 q = 1) (hb : d131098 q = 1) : d187917 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130218, d187917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130218, d187917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d130219 q = 1) (hb : d131098 q = 1) : d187918 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130219, d187918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130219, d187918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130220 q = 1) (hb : d131098 q = 1) : d187919 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130220, d187919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130220, d187919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130221 q = 1) (hb : d131098 q = 1) : d187920 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130221, d187920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130221, d187920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44218 (p : Pattern) (ha : d19845 p = 1) (hb : d131098 p = 1) : d187950 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19749 q = 1) (hb : d131098 q = 1) : d187886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19749, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44211 q ha hb
    | true =>
      simp only [d19749, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19841 q = 1) (hb : d131098 q = 1) : d187946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19841, d187946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19841, d187946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19842 q = 1) (hb : d131098 q = 1) : d187947 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19842, d187947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19842, d187947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19843 q = 1) (hb : d131098 q = 1) : d187948 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19843, d187948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19843, d187948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19844 q = 1) (hb : d131098 q = 1) : d187949 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19844, d187949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19844, d187949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19845 q = 1) (hb : d131098 q = 1) : d187950 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19845, d187950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19845, d187950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44219 (p : Pattern) (ha : d19809 p = 1) (hb : d131098 p = 1) : d187926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9389 q = 1) (hb : d131098 q = 1) : d15967 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23767 q ha hb
    | true =>
      simp only [d9389, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23761 q ha hb
  have h2 (q : Pattern) (ha : d19805 q = 1) (hb : d131098 q = 1) : d15968 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19805, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19805, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19806 q = 1) (hb : d131098 q = 1) : d15969 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19806, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19806, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9330 q = 1) (hb : d131098 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23761 q ha hb
    | true =>
      simp only [d9330, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23756 q ha hb
  have h5 (q : Pattern) (ha : d19765 q = 1) (hb : d131098 q = 1) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19765, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19766 q = 1) (hb : d131098 q = 1) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19807 q = 1) (hb : d131098 q = 1) : d15970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19807, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19807, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9297 q = 1) (hb : d131098 q = 1) : d31 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23756 q ha hb
    | true =>
      simp only [d9297, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19738 q = 1) (hb : d131098 q = 1) : d32 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19738, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19738, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19739 q = 1) (hb : d131098 q = 1) : d33 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19739, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19739, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19767 q = 1) (hb : d131098 q = 1) : d148 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19767, d148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19767, d148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19808 q = 1) (hb : d131098 q = 1) : d15971 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19808, d15971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19808, d15971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9390 q = 1) (hb : d131098 q = 1) : d18645 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d18645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9390, d18645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9391 q = 1) (hb : d131098 q = 1) : d18646 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d18646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9391, d18646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9331 q = 1) (hb : d131098 q = 1) : d18581 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9331, d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d9332 q = 1) (hb : d131098 q = 1) : d18582 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9392 q = 1) (hb : d131098 q = 1) : d18647 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d18647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9392, d18647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9298 q = 1) (hb : d131098 q = 1) : d18544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d18544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9298, d18544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d9299 q = 1) (hb : d131098 q = 1) : d18545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d18545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9299, d18545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9333 q = 1) (hb : d131098 q = 1) : d18583 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9333, d18583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9333, d18583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9393 q = 1) (hb : d131098 q = 1) : d18648 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9393, d18648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9393, d18648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d19809 q = 1) (hb : d131098 q = 1) : d187926 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19809, d187926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19809, d187926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro44220 (p : Pattern) (ha : d19815 p = 1) (hb : d131098 p = 1) : d187932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19810 q = 1) (hb : d131098 q = 1) : d187927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19810, d187927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44219 q ha hb
    | true =>
      simp only [d19810, d187927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19811 q = 1) (hb : d131098 q = 1) : d187928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19811, d187928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19811, d187928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19770 q = 1) (hb : d131098 q = 1) : d187903 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19770, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44214 q ha hb
    | true =>
      simp only [d19770, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19771 q = 1) (hb : d131098 q = 1) : d187904 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19771, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19771, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19812 q = 1) (hb : d131098 q = 1) : d187929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19812, d187929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19812, d187929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19813 q = 1) (hb : d131098 q = 1) : d187930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19813, d187930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19813, d187930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19814 q = 1) (hb : d131098 q = 1) : d187931 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19814, d187931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19814, d187931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19815 q = 1) (hb : d131098 q = 1) : d187932 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19815, d187932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19815, d187932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44221 (p : Pattern) (ha : d19833 p = 1) (hb : d131098 p = 1) : d187938 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19770 q = 1) (hb : d131098 q = 1) : d187903 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19770, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44214 q ha hb
    | true =>
      simp only [d19770, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19771 q = 1) (hb : d131098 q = 1) : d187904 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19771, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19771, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19830 q = 1) (hb : d131098 q = 1) : d187935 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19830, d187935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19830, d187935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19831 q = 1) (hb : d131098 q = 1) : d187936 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19831, d187936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19831, d187936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19832 q = 1) (hb : d131098 q = 1) : d187937 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19832, d187937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19832, d187937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19833 q = 1) (hb : d131098 q = 1) : d187938 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19833, d187938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19833, d187938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44222 (p : Pattern) (ha : d130231 p = 1) (hb : d131098 p = 1) : d187944 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19816 q = 1) (hb : d131098 q = 1) : d187933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19816, d187933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44220 q ha hb
    | true =>
      simp only [d19816, d187933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44215 q ha hb
  have h2 (q : Pattern) (ha : d130227 q = 1) (hb : d131098 q = 1) : d187934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130227, d187934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130227, d187934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19834 q = 1) (hb : d131098 q = 1) : d187939 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19834, d187939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44221 q ha hb
    | true =>
      simp only [d19834, d187939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19835 q = 1) (hb : d131098 q = 1) : d187940 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19835, d187940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19835, d187940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130228 q = 1) (hb : d131098 q = 1) : d187941 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130228, d187941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130228, d187941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130229 q = 1) (hb : d131098 q = 1) : d187942 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130229, d187942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130229, d187942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130230 q = 1) (hb : d131098 q = 1) : d187943 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130230, d187943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130230, d187943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130231 q = 1) (hb : d131098 q = 1) : d187944 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130231, d187944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130231, d187944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44223 (p : Pattern) (ha : d130237 p = 1) (hb : d131098 p = 1) : d187956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130232 q = 1) (hb : d131098 q = 1) : d187945 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130232, d187945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130232, d187945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44222 q ha hb
  have h2 (q : Pattern) (ha : d19846 q = 1) (hb : d131098 q = 1) : d187951 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19846, d187951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19846, d187951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44218 q ha hb
  have h3 (q : Pattern) (ha : d130233 q = 1) (hb : d131098 q = 1) : d187952 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130233, d187952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130233, d187952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130234 q = 1) (hb : d131098 q = 1) : d187953 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130234, d187953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130234, d187953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130235 q = 1) (hb : d131098 q = 1) : d187954 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130235, d187954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130235, d187954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130236 q = 1) (hb : d131098 q = 1) : d187955 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130236, d187955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130236, d187955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130237 q = 1) (hb : d131098 q = 1) : d187956 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130237, d187956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130237, d187956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44224 (p : Pattern) (ha : d130243 p = 1) (hb : d131098 p = 1) : d187962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19761 q = 1) (hb : d131098 q = 1) : d187898 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d19761, d187898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19761, d187898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44213 q ha hb
  have h2 (q : Pattern) (ha : d19762 q = 1) (hb : d131098 q = 1) : d187899 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d19762, d187899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19762, d187899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19763 q = 1) (hb : d131098 q = 1) : d187900 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d19763, d187900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19763, d187900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19764 q = 1) (hb : d131098 q = 1) : d187901 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d19764, d187901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19764, d187901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130222 q = 1) (hb : d131098 q = 1) : d187921 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130222, d187921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130222, d187921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44217 q ha hb
  have h6 (q : Pattern) (ha : d130223 q = 1) (hb : d131098 q = 1) : d187922 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130223, d187922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130223, d187922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130224 q = 1) (hb : d131098 q = 1) : d187923 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130224, d187923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130224, d187923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130225 q = 1) (hb : d131098 q = 1) : d187924 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130225, d187924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130225, d187924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130226 q = 1) (hb : d131098 q = 1) : d187925 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130226, d187925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130226, d187925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130238 q = 1) (hb : d131098 q = 1) : d187957 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130238, d187957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130238, d187957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44223 q ha hb
  have h11 (q : Pattern) (ha : d130239 q = 1) (hb : d131098 q = 1) : d187958 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130239, d187958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130239, d187958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d130240 q = 1) (hb : d131098 q = 1) : d187959 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130240, d187959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130240, d187959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d130241 q = 1) (hb : d131098 q = 1) : d187960 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130241, d187960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130241, d187960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d130242 q = 1) (hb : d131098 q = 1) : d187961 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130242, d187961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130242, d187961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d130243 q = 1) (hb : d131098 q = 1) : d187962 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130243, d187962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d130243, d187962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro44225 (p : Pattern) (ha : d19877 p = 1) (hb : d131098 p = 1) : d187973 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9330 q = 1) (hb : d131098 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23761 q ha hb
    | true =>
      simp only [d9330, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23756 q ha hb
  have h2 (q : Pattern) (ha : d19765 q = 1) (hb : d131098 q = 1) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19765, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19766 q = 1) (hb : d131098 q = 1) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19867 q = 1) (hb : d131098 q = 1) : d475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19867, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19867, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19876 q = 1) (hb : d131098 q = 1) : d480 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19876, d480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19876, d480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9331 q = 1) (hb : d131098 q = 1) : d18581 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9331, d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9332 q = 1) (hb : d131098 q = 1) : d18582 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9487 q = 1) (hb : d131098 q = 1) : d18740 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9487, d18740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9487, d18740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9496 q = 1) (hb : d131098 q = 1) : d18750 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9496, d18750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9496, d18750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19877 q = 1) (hb : d131098 q = 1) : d187973 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19877, d187973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19877, d187973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro44226 (p : Pattern) (ha : d19921 p = 1) (hb : d131098 p = 1) : d187996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19878 q = 1) (hb : d131098 q = 1) : d187974 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19878, d187974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44225 q ha hb
    | true =>
      simp only [d19878, d187974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19879 q = 1) (hb : d131098 q = 1) : d187975 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19879, d187975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19879, d187975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19918 q = 1) (hb : d131098 q = 1) : d187993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19918, d187993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19918, d187993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19919 q = 1) (hb : d131098 q = 1) : d187994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19919, d187994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19919, d187994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19920 q = 1) (hb : d131098 q = 1) : d187995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19920, d187995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19920, d187995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19921 q = 1) (hb : d131098 q = 1) : d187996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19921, d187996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19921, d187996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44227 (p : Pattern) (ha : d19927 p = 1) (hb : d131098 p = 1) : d188002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19922 q = 1) (hb : d131098 q = 1) : d187997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19922, d187997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44226 q ha hb
    | true =>
      simp only [d19922, d187997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19923 q = 1) (hb : d131098 q = 1) : d187998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19923, d187998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19923, d187998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19924 q = 1) (hb : d131098 q = 1) : d187999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19924, d187999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19924, d187999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19925 q = 1) (hb : d131098 q = 1) : d188000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19925, d188000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19925, d188000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19926 q = 1) (hb : d131098 q = 1) : d188001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19926, d188001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19926, d188001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19927 q = 1) (hb : d131098 q = 1) : d188002 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19927, d188002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19927, d188002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44228 (p : Pattern) (ha : d19864 p = 1) (hb : d131098 p = 1) : d187963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9475 q = 1) (hb : d131098 q = 1) : d16078 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9475, d16078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23777 q ha hb
    | true =>
      simp only [d9475, d16078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23767 q ha hb
  have h2 (q : Pattern) (ha : d19858 q = 1) (hb : d131098 q = 1) : d16079 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19858, d16079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19858, d16079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19859 q = 1) (hb : d131098 q = 1) : d16080 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19859, d16080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19859, d16080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9479 q = 1) (hb : d131098 q = 1) : d16082 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9479, d16082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23767 q ha hb
    | true =>
      simp only [d9479, d16082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23778 q ha hb
  have h5 (q : Pattern) (ha : d19860 q = 1) (hb : d131098 q = 1) : d16083 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19860, d16083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19860, d16083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19861 q = 1) (hb : d131098 q = 1) : d16084 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19861, d16084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19861, d16084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19862 q = 1) (hb : d131098 q = 1) : d16085 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19862, d16085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19862, d16085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9389 q = 1) (hb : d131098 q = 1) : d15967 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23767 q ha hb
    | true =>
      simp only [d9389, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23761 q ha hb
  have h9 (q : Pattern) (ha : d19805 q = 1) (hb : d131098 q = 1) : d15968 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19805, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19805, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19806 q = 1) (hb : d131098 q = 1) : d15969 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19806, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19806, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9330 q = 1) (hb : d131098 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23761 q ha hb
    | true =>
      simp only [d9330, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23756 q ha hb
  have h12 (q : Pattern) (ha : d19765 q = 1) (hb : d131098 q = 1) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19765, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19766 q = 1) (hb : d131098 q = 1) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19807 q = 1) (hb : d131098 q = 1) : d15970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19807, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19807, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19863 q = 1) (hb : d131098 q = 1) : d16086 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19863, d16086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19863, d16086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9476 q = 1) (hb : d131098 q = 1) : d18729 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9476, d18729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9476, d18729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d9477 q = 1) (hb : d131098 q = 1) : d18730 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9477, d18730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9477, d18730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9480 q = 1) (hb : d131098 q = 1) : d18731 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9480, d18731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9480, d18731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d9481 q = 1) (hb : d131098 q = 1) : d18732 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9481, d18732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9481, d18732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9482 q = 1) (hb : d131098 q = 1) : d18733 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9482, d18733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9482, d18733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9390 q = 1) (hb : d131098 q = 1) : d18645 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d18645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9390, d18645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d9391 q = 1) (hb : d131098 q = 1) : d18646 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d18646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9391, d18646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9331 q = 1) (hb : d131098 q = 1) : d18581 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9331, d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d9332 q = 1) (hb : d131098 q = 1) : d18582 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d9392 q = 1) (hb : d131098 q = 1) : d18647 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d18647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9392, d18647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d9483 q = 1) (hb : d131098 q = 1) : d18734 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9483, d18734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9483, d18734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d19864 q = 1) (hb : d131098 q = 1) : d187963 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19864, d187963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19864, d187963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro44229 (p : Pattern) (ha : d19869 p = 1) (hb : d131098 p = 1) : d187966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9389 q = 1) (hb : d131098 q = 1) : d15967 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23767 q ha hb
    | true =>
      simp only [d9389, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23761 q ha hb
  have h2 (q : Pattern) (ha : d19805 q = 1) (hb : d131098 q = 1) : d15968 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19805, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19805, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19806 q = 1) (hb : d131098 q = 1) : d15969 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19806, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19806, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9330 q = 1) (hb : d131098 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23761 q ha hb
    | true =>
      simp only [d9330, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23756 q ha hb
  have h5 (q : Pattern) (ha : d19765 q = 1) (hb : d131098 q = 1) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19765, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19766 q = 1) (hb : d131098 q = 1) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19807 q = 1) (hb : d131098 q = 1) : d15970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19807, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19807, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19867 q = 1) (hb : d131098 q = 1) : d475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19867, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19867, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19868 q = 1) (hb : d131098 q = 1) : d16035 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19868, d16035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19868, d16035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9390 q = 1) (hb : d131098 q = 1) : d18645 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d18645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9390, d18645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9391 q = 1) (hb : d131098 q = 1) : d18646 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d18646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9391, d18646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9331 q = 1) (hb : d131098 q = 1) : d18581 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9331, d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9332 q = 1) (hb : d131098 q = 1) : d18582 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9392 q = 1) (hb : d131098 q = 1) : d18647 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d18647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9392, d18647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9487 q = 1) (hb : d131098 q = 1) : d18740 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9487, d18740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9487, d18740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d9488 q = 1) (hb : d131098 q = 1) : d18741 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9488, d18741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9488, d18741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19869 q = 1) (hb : d131098 q = 1) : d187966 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19869, d187966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19869, d187966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro44230 (p : Pattern) (ha : d19875 p = 1) (hb : d131098 p = 1) : d187972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19865 q = 1) (hb : d131098 q = 1) : d187964 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19865, d187964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44228 q ha hb
    | true =>
      simp only [d19865, d187964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19866 q = 1) (hb : d131098 q = 1) : d187965 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19866, d187965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19866, d187965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19870 q = 1) (hb : d131098 q = 1) : d187967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19870, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44229 q ha hb
    | true =>
      simp only [d19870, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19871 q = 1) (hb : d131098 q = 1) : d187968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19871, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19871, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19872 q = 1) (hb : d131098 q = 1) : d187969 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19872, d187969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19872, d187969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19873 q = 1) (hb : d131098 q = 1) : d187970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19873, d187970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19873, d187970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19874 q = 1) (hb : d131098 q = 1) : d187971 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19874, d187971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19874, d187971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19875 q = 1) (hb : d131098 q = 1) : d187972 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19875, d187972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19875, d187972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44231 (p : Pattern) (ha : d19883 p = 1) (hb : d131098 p = 1) : d187979 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19870 q = 1) (hb : d131098 q = 1) : d187967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19870, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44229 q ha hb
    | true =>
      simp only [d19870, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19871 q = 1) (hb : d131098 q = 1) : d187968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19871, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19871, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19878 q = 1) (hb : d131098 q = 1) : d187974 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19878, d187974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44225 q ha hb
    | true =>
      simp only [d19878, d187974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19879 q = 1) (hb : d131098 q = 1) : d187975 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19879, d187975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19879, d187975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19880 q = 1) (hb : d131098 q = 1) : d187976 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19880, d187976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19880, d187976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19881 q = 1) (hb : d131098 q = 1) : d187977 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19881, d187977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19881, d187977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19882 q = 1) (hb : d131098 q = 1) : d187978 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19882, d187978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19882, d187978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19883 q = 1) (hb : d131098 q = 1) : d187979 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19883, d187979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19883, d187979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44232 (p : Pattern) (ha : d19910 p = 1) (hb : d131098 p = 1) : d187985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19870 q = 1) (hb : d131098 q = 1) : d187967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19870, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44229 q ha hb
    | true =>
      simp only [d19870, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19871 q = 1) (hb : d131098 q = 1) : d187968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19871, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19871, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19907 q = 1) (hb : d131098 q = 1) : d187982 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19907, d187982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19907, d187982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19908 q = 1) (hb : d131098 q = 1) : d187983 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19908, d187983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19908, d187983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19909 q = 1) (hb : d131098 q = 1) : d187984 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19909, d187984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19909, d187984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19910 q = 1) (hb : d131098 q = 1) : d187985 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19910, d187985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19910, d187985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44233 (p : Pattern) (ha : d130248 p = 1) (hb : d131098 p = 1) : d187991 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19884 q = 1) (hb : d131098 q = 1) : d187980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19884, d187980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44230 q ha hb
    | true =>
      simp only [d19884, d187980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44231 q ha hb
  have h2 (q : Pattern) (ha : d130244 q = 1) (hb : d131098 q = 1) : d187981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130244, d187981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130244, d187981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19911 q = 1) (hb : d131098 q = 1) : d187986 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19911, d187986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44232 q ha hb
    | true =>
      simp only [d19911, d187986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19912 q = 1) (hb : d131098 q = 1) : d187987 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19912, d187987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19912, d187987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130245 q = 1) (hb : d131098 q = 1) : d187988 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130245, d187988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130245, d187988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130246 q = 1) (hb : d131098 q = 1) : d187989 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130246, d187989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130246, d187989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130247 q = 1) (hb : d131098 q = 1) : d187990 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130247, d187990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130247, d187990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130248 q = 1) (hb : d131098 q = 1) : d187991 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130248, d187991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130248, d187991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44234 (p : Pattern) (ha : d130254 p = 1) (hb : d131098 p = 1) : d188008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130249 q = 1) (hb : d131098 q = 1) : d187992 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130249, d187992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130249, d187992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44233 q ha hb
  have h2 (q : Pattern) (ha : d19928 q = 1) (hb : d131098 q = 1) : d188003 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19928, d188003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19928, d188003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44227 q ha hb
  have h3 (q : Pattern) (ha : d130250 q = 1) (hb : d131098 q = 1) : d188004 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130250, d188004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130250, d188004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130251 q = 1) (hb : d131098 q = 1) : d188005 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130251, d188005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130251, d188005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130252 q = 1) (hb : d131098 q = 1) : d188006 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130252, d188006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130252, d188006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130253 q = 1) (hb : d131098 q = 1) : d188007 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130253, d188007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130253, d188007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130254 q = 1) (hb : d131098 q = 1) : d188008 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130254, d188008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130254, d188008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44235 (p : Pattern) (ha : d130260 p = 1) (hb : d131098 p = 1) : d188014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130255 q = 1) (hb : d131098 q = 1) : d188009 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130255, d188009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130255, d188009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44234 q ha hb
  have h2 (q : Pattern) (ha : d130256 q = 1) (hb : d131098 q = 1) : d188010 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130256, d188010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130256, d188010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130257 q = 1) (hb : d131098 q = 1) : d188011 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130257, d188011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130257, d188011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130258 q = 1) (hb : d131098 q = 1) : d188012 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130258, d188012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130258, d188012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130259 q = 1) (hb : d131098 q = 1) : d188013 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130259, d188013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130259, d188013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130260 q = 1) (hb : d131098 q = 1) : d188014 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130260, d188014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130260, d188014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44236 (p : Pattern) (ha : d19965 p = 1) (hb : d131098 p = 1) : d188026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9624 q = 1) (hb : d131098 q = 1) : d763 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23787 q ha hb
    | true =>
      simp only [d9624, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23788 q ha hb
  have h2 (q : Pattern) (ha : d19948 q = 1) (hb : d131098 q = 1) : d764 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19948, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19948, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19949 q = 1) (hb : d131098 q = 1) : d765 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19949, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19949, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19955 q = 1) (hb : d131098 q = 1) : d767 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19955, d767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19955, d767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19964 q = 1) (hb : d131098 q = 1) : d772 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19964, d772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19964, d772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9625 q = 1) (hb : d131098 q = 1) : d18875 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d18875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9625, d18875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9626 q = 1) (hb : d131098 q = 1) : d18876 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d18876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9626, d18876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9632 q = 1) (hb : d131098 q = 1) : d18884 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9632, d18884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9632, d18884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9641 q = 1) (hb : d131098 q = 1) : d18894 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9641, d18894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9641, d18894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19965 q = 1) (hb : d131098 q = 1) : d188026 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19965, d188026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19965, d188026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro44237 (p : Pattern) (ha : d20011 p = 1) (hb : d131098 p = 1) : d188049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19966 q = 1) (hb : d131098 q = 1) : d188027 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19966, d188027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44236 q ha hb
    | true =>
      simp only [d19966, d188027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19967 q = 1) (hb : d131098 q = 1) : d188028 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19967, d188028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19967, d188028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20008 q = 1) (hb : d131098 q = 1) : d188046 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20008, d188046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20008, d188046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20009 q = 1) (hb : d131098 q = 1) : d188047 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20009, d188047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20009, d188047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20010 q = 1) (hb : d131098 q = 1) : d188048 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20010, d188048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20010, d188048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20011 q = 1) (hb : d131098 q = 1) : d188049 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20011, d188049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20011, d188049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44238 (p : Pattern) (ha : d20017 p = 1) (hb : d131098 p = 1) : d188055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20012 q = 1) (hb : d131098 q = 1) : d188050 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20012, d188050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44237 q ha hb
    | true =>
      simp only [d20012, d188050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20013 q = 1) (hb : d131098 q = 1) : d188051 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20013, d188051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20013, d188051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20014 q = 1) (hb : d131098 q = 1) : d188052 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20014, d188052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20014, d188052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20015 q = 1) (hb : d131098 q = 1) : d188053 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20015, d188053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20015, d188053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20016 q = 1) (hb : d131098 q = 1) : d188054 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20016, d188054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20016, d188054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20017 q = 1) (hb : d131098 q = 1) : d188055 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20017, d188055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20017, d188055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44239 (p : Pattern) (ha : d19952 p = 1) (hb : d131098 p = 1) : d188016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9609 q = 1) (hb : d131098 q = 1) : d16275 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9609, d16275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23792 q ha hb
    | true =>
      simp only [d9609, d16275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23793 q ha hb
  have h2 (q : Pattern) (ha : d19941 q = 1) (hb : d131098 q = 1) : d16276 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19941, d16276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19941, d16276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19942 q = 1) (hb : d131098 q = 1) : d16277 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19942, d16277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19942, d16277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9614 q = 1) (hb : d131098 q = 1) : d16279 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9614, d16279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23793 q ha hb
    | true =>
      simp only [d9614, d16279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23794 q ha hb
  have h5 (q : Pattern) (ha : d19943 q = 1) (hb : d131098 q = 1) : d16280 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19943, d16280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19943, d16280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19944 q = 1) (hb : d131098 q = 1) : d16281 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19944, d16281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19944, d16281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19945 q = 1) (hb : d131098 q = 1) : d16282 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19945, d16282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19945, d16282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9620 q = 1) (hb : d131098 q = 1) : d16228 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23793 q ha hb
    | true =>
      simp only [d9620, d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23787 q ha hb
  have h9 (q : Pattern) (ha : d19946 q = 1) (hb : d131098 q = 1) : d16229 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19946, d16229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19946, d16229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19947 q = 1) (hb : d131098 q = 1) : d16230 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19947, d16230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19947, d16230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9624 q = 1) (hb : d131098 q = 1) : d763 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23787 q ha hb
    | true =>
      simp only [d9624, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23788 q ha hb
  have h12 (q : Pattern) (ha : d19948 q = 1) (hb : d131098 q = 1) : d764 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19948, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19948, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19949 q = 1) (hb : d131098 q = 1) : d765 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19949, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19949, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19950 q = 1) (hb : d131098 q = 1) : d16231 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19950, d16231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19950, d16231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19951 q = 1) (hb : d131098 q = 1) : d16283 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19951, d16283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19951, d16283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9610 q = 1) (hb : d131098 q = 1) : d18868 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9610, d18868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9610, d18868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d9611 q = 1) (hb : d131098 q = 1) : d18869 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9611, d18869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9611, d18869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9615 q = 1) (hb : d131098 q = 1) : d18870 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9615, d18870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9615, d18870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d9616 q = 1) (hb : d131098 q = 1) : d18871 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9616, d18871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9616, d18871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9617 q = 1) (hb : d131098 q = 1) : d18872 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9617, d18872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9617, d18872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9621 q = 1) (hb : d131098 q = 1) : d18873 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9621, d18873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9621, d18873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d9622 q = 1) (hb : d131098 q = 1) : d18874 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9622, d18874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9622, d18874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9625 q = 1) (hb : d131098 q = 1) : d18875 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d18875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9625, d18875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d9626 q = 1) (hb : d131098 q = 1) : d18876 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d18876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9626, d18876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d9627 q = 1) (hb : d131098 q = 1) : d18877 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9627, d18877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9627, d18877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d9628 q = 1) (hb : d131098 q = 1) : d18878 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9628, d18878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9628, d18878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d19952 q = 1) (hb : d131098 q = 1) : d188016 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19952, d188016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19952, d188016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro44240 (p : Pattern) (ha : d19957 p = 1) (hb : d131098 p = 1) : d188019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9620 q = 1) (hb : d131098 q = 1) : d16228 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23793 q ha hb
    | true =>
      simp only [d9620, d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23787 q ha hb
  have h2 (q : Pattern) (ha : d19946 q = 1) (hb : d131098 q = 1) : d16229 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19946, d16229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19946, d16229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19947 q = 1) (hb : d131098 q = 1) : d16230 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19947, d16230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19947, d16230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9624 q = 1) (hb : d131098 q = 1) : d763 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23787 q ha hb
    | true =>
      simp only [d9624, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23788 q ha hb
  have h5 (q : Pattern) (ha : d19948 q = 1) (hb : d131098 q = 1) : d764 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19948, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19948, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19949 q = 1) (hb : d131098 q = 1) : d765 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19949, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19949, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19950 q = 1) (hb : d131098 q = 1) : d16231 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19950, d16231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19950, d16231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19955 q = 1) (hb : d131098 q = 1) : d767 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19955, d767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19955, d767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19956 q = 1) (hb : d131098 q = 1) : d16232 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19956, d16232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19956, d16232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9621 q = 1) (hb : d131098 q = 1) : d18873 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9621, d18873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9621, d18873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9622 q = 1) (hb : d131098 q = 1) : d18874 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9622, d18874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9622, d18874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9625 q = 1) (hb : d131098 q = 1) : d18875 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d18875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9625, d18875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9626 q = 1) (hb : d131098 q = 1) : d18876 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d18876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9626, d18876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9627 q = 1) (hb : d131098 q = 1) : d18877 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9627, d18877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9627, d18877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9632 q = 1) (hb : d131098 q = 1) : d18884 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9632, d18884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9632, d18884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d9633 q = 1) (hb : d131098 q = 1) : d18885 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9633, d18885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9633, d18885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19957 q = 1) (hb : d131098 q = 1) : d188019 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19957, d188019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19957, d188019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro44241 (p : Pattern) (ha : d19963 p = 1) (hb : d131098 p = 1) : d188025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19953 q = 1) (hb : d131098 q = 1) : d188017 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19953, d188017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44239 q ha hb
    | true =>
      simp only [d19953, d188017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19954 q = 1) (hb : d131098 q = 1) : d188018 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19954, d188018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19954, d188018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19958 q = 1) (hb : d131098 q = 1) : d188020 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19958, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44240 q ha hb
    | true =>
      simp only [d19958, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19959 q = 1) (hb : d131098 q = 1) : d188021 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19959, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19959, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19960 q = 1) (hb : d131098 q = 1) : d188022 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19960, d188022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19960, d188022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19961 q = 1) (hb : d131098 q = 1) : d188023 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19961, d188023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19961, d188023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19962 q = 1) (hb : d131098 q = 1) : d188024 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19962, d188024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19962, d188024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19963 q = 1) (hb : d131098 q = 1) : d188025 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19963, d188025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19963, d188025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44242 (p : Pattern) (ha : d19971 p = 1) (hb : d131098 p = 1) : d188032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19958 q = 1) (hb : d131098 q = 1) : d188020 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19958, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44240 q ha hb
    | true =>
      simp only [d19958, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19959 q = 1) (hb : d131098 q = 1) : d188021 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19959, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19959, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19966 q = 1) (hb : d131098 q = 1) : d188027 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19966, d188027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44236 q ha hb
    | true =>
      simp only [d19966, d188027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19967 q = 1) (hb : d131098 q = 1) : d188028 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19967, d188028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19967, d188028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19968 q = 1) (hb : d131098 q = 1) : d188029 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19968, d188029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19968, d188029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19969 q = 1) (hb : d131098 q = 1) : d188030 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19969, d188030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19969, d188030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19970 q = 1) (hb : d131098 q = 1) : d188031 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19970, d188031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19970, d188031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19971 q = 1) (hb : d131098 q = 1) : d188032 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19971, d188032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19971, d188032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44243 (p : Pattern) (ha : d20000 p = 1) (hb : d131098 p = 1) : d188038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19958 q = 1) (hb : d131098 q = 1) : d188020 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19958, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44240 q ha hb
    | true =>
      simp only [d19958, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19959 q = 1) (hb : d131098 q = 1) : d188021 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19959, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19959, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19997 q = 1) (hb : d131098 q = 1) : d188035 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19997, d188035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19997, d188035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19998 q = 1) (hb : d131098 q = 1) : d188036 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19998, d188036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19998, d188036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19999 q = 1) (hb : d131098 q = 1) : d188037 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19999, d188037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19999, d188037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20000 q = 1) (hb : d131098 q = 1) : d188038 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20000, d188038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20000, d188038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44244 (p : Pattern) (ha : d130266 p = 1) (hb : d131098 p = 1) : d188044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19972 q = 1) (hb : d131098 q = 1) : d188033 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19972, d188033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44241 q ha hb
    | true =>
      simp only [d19972, d188033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44242 q ha hb
  have h2 (q : Pattern) (ha : d130262 q = 1) (hb : d131098 q = 1) : d188034 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130262, d188034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130262, d188034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20001 q = 1) (hb : d131098 q = 1) : d188039 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20001, d188039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44243 q ha hb
    | true =>
      simp only [d20001, d188039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20002 q = 1) (hb : d131098 q = 1) : d188040 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20002, d188040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20002, d188040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130263 q = 1) (hb : d131098 q = 1) : d188041 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130263, d188041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130263, d188041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130264 q = 1) (hb : d131098 q = 1) : d188042 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130264, d188042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130264, d188042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130265 q = 1) (hb : d131098 q = 1) : d188043 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130265, d188043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130265, d188043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130266 q = 1) (hb : d131098 q = 1) : d188044 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130266, d188044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130266, d188044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44245 (p : Pattern) (ha : d130272 p = 1) (hb : d131098 p = 1) : d188061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130267 q = 1) (hb : d131098 q = 1) : d188045 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130267, d188045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130267, d188045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44244 q ha hb
  have h2 (q : Pattern) (ha : d20018 q = 1) (hb : d131098 q = 1) : d188056 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20018, d188056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20018, d188056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44238 q ha hb
  have h3 (q : Pattern) (ha : d130268 q = 1) (hb : d131098 q = 1) : d188057 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130268, d188057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130268, d188057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130269 q = 1) (hb : d131098 q = 1) : d188058 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130269, d188058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130269, d188058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130270 q = 1) (hb : d131098 q = 1) : d188059 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130270, d188059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130270, d188059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130271 q = 1) (hb : d131098 q = 1) : d188060 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130271, d188060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130271, d188060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130272 q = 1) (hb : d131098 q = 1) : d188061 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130272, d188061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130272, d188061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44246 (p : Pattern) (ha : d130278 p = 1) (hb : d131098 p = 1) : d188067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130273 q = 1) (hb : d131098 q = 1) : d188062 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130273, d188062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130273, d188062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44245 q ha hb
  have h2 (q : Pattern) (ha : d130274 q = 1) (hb : d131098 q = 1) : d188063 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130274, d188063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130274, d188063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130275 q = 1) (hb : d131098 q = 1) : d188064 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130275, d188064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130275, d188064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130276 q = 1) (hb : d131098 q = 1) : d188065 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130276, d188065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130276, d188065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130277 q = 1) (hb : d131098 q = 1) : d188066 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130277, d188066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130277, d188066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130278 q = 1) (hb : d131098 q = 1) : d188067 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130278, d188067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130278, d188067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44247 (p : Pattern) (ha : d20059 p = 1) (hb : d131098 p = 1) : d188080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9870 q = 1) (hb : d131098 q = 1) : d16451 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23803 q ha hb
    | true =>
      simp only [d9870, d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23804 q ha hb
  have h2 (q : Pattern) (ha : d20055 q = 1) (hb : d131098 q = 1) : d16452 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20055, d16452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20055, d16452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20056 q = 1) (hb : d131098 q = 1) : d16453 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20056, d16453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20056, d16453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20057 q = 1) (hb : d131098 q = 1) : d16454 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20057, d16454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20057, d16454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20058 q = 1) (hb : d131098 q = 1) : d16459 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20058, d16459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20058, d16459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9871 q = 1) (hb : d131098 q = 1) : d19088 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9871, d19088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9871, d19088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9872 q = 1) (hb : d131098 q = 1) : d19089 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9872, d19089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9872, d19089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9873 q = 1) (hb : d131098 q = 1) : d19090 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9873, d19090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9873, d19090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9874 q = 1) (hb : d131098 q = 1) : d19091 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9874, d19091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9874, d19091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d20059 q = 1) (hb : d131098 q = 1) : d188080 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20059, d188080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20059, d188080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro44248 (p : Pattern) (ha : d20114 p = 1) (hb : d131098 p = 1) : d188106 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20060 q = 1) (hb : d131098 q = 1) : d188081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20060, d188081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44247 q ha hb
    | true =>
      simp only [d20060, d188081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20061 q = 1) (hb : d131098 q = 1) : d188082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20061, d188082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20061, d188082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20111 q = 1) (hb : d131098 q = 1) : d188103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20111, d188103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20111, d188103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20112 q = 1) (hb : d131098 q = 1) : d188104 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20112, d188104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20112, d188104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20113 q = 1) (hb : d131098 q = 1) : d188105 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20113, d188105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20113, d188105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20114 q = 1) (hb : d131098 q = 1) : d188106 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20114, d188106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20114, d188106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44249 (p : Pattern) (ha : d20120 p = 1) (hb : d131098 p = 1) : d188112 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20115 q = 1) (hb : d131098 q = 1) : d188107 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20115, d188107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44248 q ha hb
    | true =>
      simp only [d20115, d188107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20116 q = 1) (hb : d131098 q = 1) : d188108 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20116, d188108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20116, d188108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20117 q = 1) (hb : d131098 q = 1) : d188109 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20117, d188109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20117, d188109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20118 q = 1) (hb : d131098 q = 1) : d188110 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20118, d188110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20118, d188110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20119 q = 1) (hb : d131098 q = 1) : d188111 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20119, d188111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20119, d188111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20120 q = 1) (hb : d131098 q = 1) : d188112 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20120, d188112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20120, d188112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
