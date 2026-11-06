import NetHack.Soko22Hazard87.AndIntroBlocks0280
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro70250 (p : Pattern) (ha : d263643 p = 1) (hb : d279250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263616 q = 1) (hb : d279225 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263616, d279225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70245 q ha hb
    | true =>
      simp only [d263616, d279225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263617 q = 1) (hb : d279226 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263617, d279226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263617, d279226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263618 q = 1) (hb : d279227 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263618, d279227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263618, d279227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263619 q = 1) (hb : d279228 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263619, d279228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263619, d279228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263642 q = 1) (hb : d279249 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263642, d279249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263642, d279249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101733 q = 1) (hb : d270516 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d101733, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70247 q ha hb
    | true =>
      simp only [d101733, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101735 q = 1) (hb : d270517 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d101735, d270517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101735, d270517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123554 q = 1) (hb : d270518 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123554, d270518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123554, d270518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123555 q = 1) (hb : d270519 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123555, d270519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123555, d270519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123556 q = 1) (hb : d270520 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123556, d270520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d123556, d270520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d263643 q = 1) (hb : d279250 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263643, d279250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263643, d279250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro70251 (p : Pattern) (ha : d263649 p = 1) (hb : d279256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263623 q = 1) (hb : d279232 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263623, d279232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70242 q ha hb
    | true =>
      simp only [d263623, d279232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70246 q ha hb
  have h2 (q : Pattern) (ha : d263624 q = 1) (hb : d279233 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263624, d279233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263624, d279233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263625 q = 1) (hb : d279234 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263625, d279234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263625, d279234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263638 q = 1) (hb : d279245 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263638, d279245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70246 q ha hb
    | true =>
      simp only [d263638, d279245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70249 q ha hb
  have h5 (q : Pattern) (ha : d263639 q = 1) (hb : d279246 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263639, d279246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263639, d279246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263640 q = 1) (hb : d279247 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263640, d279247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263640, d279247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263641 q = 1) (hb : d279248 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263641, d279248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263641, d279248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263644 q = 1) (hb : d279251 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263644, d279251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70246 q ha hb
    | true =>
      simp only [d263644, d279251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70250 q ha hb
  have h9 (q : Pattern) (ha : d263645 q = 1) (hb : d279252 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263645, d279252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263645, d279252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263646 q = 1) (hb : d279253 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263646, d279253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263646, d279253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263647 q = 1) (hb : d279254 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263647, d279254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263647, d279254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d263648 q = 1) (hb : d279255 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263648, d279255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263648, d279255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263649 q = 1) (hb : d279256 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263649, d279256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263649, d279256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro70252 (p : Pattern) (ha : d263653 p = 1) (hb : d279260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263644 q = 1) (hb : d279251 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263644, d279251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70246 q ha hb
    | true =>
      simp only [d263644, d279251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70250 q ha hb
  have h2 (q : Pattern) (ha : d263645 q = 1) (hb : d279252 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263645, d279252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263645, d279252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263646 q = 1) (hb : d279253 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263646, d279253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263646, d279253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263647 q = 1) (hb : d279254 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263647, d279254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263647, d279254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263652 q = 1) (hb : d279259 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263652, d279259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263652, d279259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263653 q = 1) (hb : d279260 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263653, d279260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263653, d279260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70253 (p : Pattern) (ha : d263659 p = 1) (hb : d279266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263650 q = 1) (hb : d279257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263650, d279257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70251 q ha hb
    | true =>
      simp only [d263650, d279257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263651 q = 1) (hb : d279258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263651, d279258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263651, d279258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263654 q = 1) (hb : d279261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70252 q ha hb
    | true =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263655 q = 1) (hb : d279262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263656 q = 1) (hb : d279263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263656, d279263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263656, d279263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263657 q = 1) (hb : d279264 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263657, d279264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263657, d279264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263658 q = 1) (hb : d279265 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263658, d279265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263658, d279265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263659 q = 1) (hb : d279266 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263659, d279266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263659, d279266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70254 (p : Pattern) (ha : d263663 p = 1) (hb : d279270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263654 q = 1) (hb : d279261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70252 q ha hb
    | true =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263655 q = 1) (hb : d279262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263660 q = 1) (hb : d279267 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263660, d279267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263660, d279267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263661 q = 1) (hb : d279268 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263661, d279268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263661, d279268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263662 q = 1) (hb : d279269 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263662, d279269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263662, d279269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263663 q = 1) (hb : d279270 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263663, d279270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263663, d279270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70255 (p : Pattern) (ha : d263669 p = 1) (hb : d279276 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263664 q = 1) (hb : d279271 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263664, d279271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70253 q ha hb
    | true =>
      simp only [d263664, d279271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70254 q ha hb
  have h2 (q : Pattern) (ha : d263665 q = 1) (hb : d279272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263665, d279272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263665, d279272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263666 q = 1) (hb : d279273 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263666, d279273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263666, d279273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263667 q = 1) (hb : d279274 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263667, d279274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263667, d279274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263668 q = 1) (hb : d279275 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263668, d279275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263668, d279275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263669 q = 1) (hb : d279276 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263669, d279276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263669, d279276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70256 (p : Pattern) (ha : d263672 p = 1) (hb : d279279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263650 q = 1) (hb : d279257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263650, d279257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70251 q ha hb
    | true =>
      simp only [d263650, d279257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263651 q = 1) (hb : d279258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263651, d279258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263651, d279258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263654 q = 1) (hb : d279261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70252 q ha hb
    | true =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263655 q = 1) (hb : d279262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263656 q = 1) (hb : d279263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263656, d279263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263656, d279263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263657 q = 1) (hb : d279264 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263657, d279264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263657, d279264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263658 q = 1) (hb : d279265 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263658, d279265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263658, d279265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263672 q = 1) (hb : d279279 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263672, d279279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263672, d279279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro70257 (p : Pattern) (ha : d263673 p = 1) (hb : d279280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263654 q = 1) (hb : d279261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70252 q ha hb
    | true =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263655 q = 1) (hb : d279262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263660 q = 1) (hb : d279267 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263660, d279267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263660, d279267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263661 q = 1) (hb : d279268 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263661, d279268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263661, d279268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263662 q = 1) (hb : d279269 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263662, d279269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263662, d279269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263673 q = 1) (hb : d279280 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263673, d279280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263673, d279280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70258 (p : Pattern) (ha : d263679 p = 1) (hb : d279286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263664 q = 1) (hb : d279271 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263664, d279271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70253 q ha hb
    | true =>
      simp only [d263664, d279271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70254 q ha hb
  have h2 (q : Pattern) (ha : d263665 q = 1) (hb : d279272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263665, d279272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263665, d279272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263666 q = 1) (hb : d279273 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263666, d279273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263666, d279273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263667 q = 1) (hb : d279274 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263667, d279274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263667, d279274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263668 q = 1) (hb : d279275 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263668, d279275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263668, d279275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263674 q = 1) (hb : d279281 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263674, d279281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70256 q ha hb
    | true =>
      simp only [d263674, d279281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70257 q ha hb
  have h7 (q : Pattern) (ha : d263675 q = 1) (hb : d279282 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263675, d279282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263675, d279282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263676 q = 1) (hb : d279283 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263676, d279283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263676, d279283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263677 q = 1) (hb : d279284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263677, d279284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263677, d279284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263678 q = 1) (hb : d279285 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263678, d279285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263678, d279285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263679 q = 1) (hb : d279286 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263679, d279286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263679, d279286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro70259 (p : Pattern) (ha : d263684 p = 1) (hb : d279291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263650 q = 1) (hb : d279257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263650, d279257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70251 q ha hb
    | true =>
      simp only [d263650, d279257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263651 q = 1) (hb : d279258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263651, d279258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263651, d279258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263654 q = 1) (hb : d279261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70252 q ha hb
    | true =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263655 q = 1) (hb : d279262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263656 q = 1) (hb : d279263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263656, d279263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263656, d279263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263657 q = 1) (hb : d279264 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263657, d279264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263657, d279264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263683 q = 1) (hb : d279290 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263683, d279290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263683, d279290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263684 q = 1) (hb : d279291 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263684, d279291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263684, d279291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70260 (p : Pattern) (ha : d263686 p = 1) (hb : d279293 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263654 q = 1) (hb : d279261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70252 q ha hb
    | true =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263655 q = 1) (hb : d279262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263660 q = 1) (hb : d279267 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263660, d279267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263660, d279267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263661 q = 1) (hb : d279268 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263661, d279268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263661, d279268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263685 q = 1) (hb : d279292 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263685, d279292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263685, d279292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263686 q = 1) (hb : d279293 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263686, d279293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263686, d279293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70261 (p : Pattern) (ha : d263693 p = 1) (hb : d279300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263650 q = 1) (hb : d279257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263650, d279257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70251 q ha hb
    | true =>
      simp only [d263650, d279257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263651 q = 1) (hb : d279258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263651, d279258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263651, d279258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263654 q = 1) (hb : d279261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70252 q ha hb
    | true =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263655 q = 1) (hb : d279262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263656 q = 1) (hb : d279263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263656, d279263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263656, d279263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263691 q = 1) (hb : d279298 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263691, d279298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263691, d279298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263692 q = 1) (hb : d279299 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263692, d279299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263692, d279299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263693 q = 1) (hb : d279300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263693, d279300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263693, d279300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70262 (p : Pattern) (ha : d263696 p = 1) (hb : d279303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263654 q = 1) (hb : d279261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70252 q ha hb
    | true =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263655 q = 1) (hb : d279262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263660 q = 1) (hb : d279267 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263660, d279267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263660, d279267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263694 q = 1) (hb : d279301 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263694, d279301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263694, d279301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263695 q = 1) (hb : d279302 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263695, d279302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263695, d279302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263696 q = 1) (hb : d279303 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263696, d279303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263696, d279303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70263 (p : Pattern) (ha : d263705 p = 1) (hb : d279310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263590 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263598 q = 1) (hb : d279210 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263598, d279210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70241 q ha hb
    | true =>
      simp only [d263598, d279210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d263599 q = 1) (hb : d279211 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263599, d279211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263599, d279211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d263600 q = 1) (hb : d279212 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263600, d279212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263600, d279212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263601 q = 1) (hb : d279213 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263601, d279213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263601, d279213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d263602 q = 1) (hb : d279214 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263602, d279214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263602, d279214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263621 q = 1) (hb : d279230 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263621, d279230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263621, d279230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d263705 q = 1) (hb : d279310 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263705, d279310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263705, d279310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70264 (p : Pattern) (ha : d263711 p = 1) (hb : d279316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263701 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263702 q = 1) (hb : d279307 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263702, d279307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263702, d279307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70242 q ha hb
  have h3 (q : Pattern) (ha : d263703 q = 1) (hb : d279308 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263703, d279308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263703, d279308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263704 q = 1) (hb : d279309 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263704, d279309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263704, d279309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263706 q = 1) (hb : d279311 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263706, d279311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70242 q ha hb
    | true =>
      simp only [d263706, d279311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70263 q ha hb
  have h6 (q : Pattern) (ha : d263707 q = 1) (hb : d279312 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263707, d279312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263707, d279312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263708 q = 1) (hb : d279313 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263708, d279313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263708, d279313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263709 q = 1) (hb : d279314 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263709, d279314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263709, d279314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263623 q = 1) (hb : d279232 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263623, d279232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70242 q ha hb
    | true =>
      simp only [d263623, d279232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70246 q ha hb
  have h10 (q : Pattern) (ha : d263624 q = 1) (hb : d279233 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263624, d279233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263624, d279233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263625 q = 1) (hb : d279234 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263625, d279234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263625, d279234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d263638 q = 1) (hb : d279245 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263638, d279245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70246 q ha hb
    | true =>
      simp only [d263638, d279245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70249 q ha hb
  have h13 (q : Pattern) (ha : d263639 q = 1) (hb : d279246 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263639, d279246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263639, d279246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263640 q = 1) (hb : d279247 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263640, d279247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263640, d279247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d263641 q = 1) (hb : d279248 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263641, d279248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263641, d279248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d263710 q = 1) (hb : d279315 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263710, d279315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263710, d279315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d263711 q = 1) (hb : d279316 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263711, d279316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263711, d279316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro70265 (p : Pattern) (ha : d263716 p = 1) (hb : d279321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263623 q = 1) (hb : d279232 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263623, d279232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70242 q ha hb
    | true =>
      simp only [d263623, d279232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70246 q ha hb
  have h2 (q : Pattern) (ha : d263624 q = 1) (hb : d279233 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263624, d279233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263624, d279233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263625 q = 1) (hb : d279234 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263625, d279234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263625, d279234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263638 q = 1) (hb : d279245 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263638, d279245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70246 q ha hb
    | true =>
      simp only [d263638, d279245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70249 q ha hb
  have h5 (q : Pattern) (ha : d263639 q = 1) (hb : d279246 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263639, d279246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263639, d279246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263640 q = 1) (hb : d279247 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263640, d279247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263640, d279247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263641 q = 1) (hb : d279248 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263641, d279248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263641, d279248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263714 q = 1) (hb : d279319 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263714, d279319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263714, d279319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263715 q = 1) (hb : d279320 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263715, d279320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263715, d279320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263716 q = 1) (hb : d279321 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263716, d279321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263716, d279321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro70266 (p : Pattern) (ha : d263722 p = 1) (hb : d279327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263712 q = 1) (hb : d279317 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263712, d279317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70264 q ha hb
    | true =>
      simp only [d263712, d279317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263713 q = 1) (hb : d279318 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263713, d279318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263713, d279318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263717 q = 1) (hb : d279322 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263717, d279322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70265 q ha hb
    | true =>
      simp only [d263717, d279322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263718 q = 1) (hb : d279323 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263718, d279323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263718, d279323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263719 q = 1) (hb : d279324 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263719, d279324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263719, d279324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263720 q = 1) (hb : d279325 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263720, d279325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263720, d279325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263721 q = 1) (hb : d279326 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263721, d279326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263721, d279326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263722 q = 1) (hb : d279327 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263722, d279327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263722, d279327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70267 (p : Pattern) (ha : d263726 p = 1) (hb : d279331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263717 q = 1) (hb : d279322 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263717, d279322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70265 q ha hb
    | true =>
      simp only [d263717, d279322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263718 q = 1) (hb : d279323 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263718, d279323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263718, d279323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263654 q = 1) (hb : d279261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70252 q ha hb
    | true =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263655 q = 1) (hb : d279262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263723 q = 1) (hb : d279328 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263723, d279328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263723, d279328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263724 q = 1) (hb : d279329 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263724, d279329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263724, d279329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263725 q = 1) (hb : d279330 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263725, d279330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263725, d279330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263726 q = 1) (hb : d279331 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263726, d279331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263726, d279331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70268 (p : Pattern) (ha : d263732 p = 1) (hb : d279209 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35362 q = 1) (hb : d263592 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35362, d263592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35362, d263592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70240 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d35363 q = 1) (hb : d263593 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35363, d263593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35363, d263593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263729 q = 1) (hb : d279206 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d263729, d279206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d263729, d279206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263730 q = 1) (hb : d279207 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d263730, d279207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263730, d279207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263731 q = 1) (hb : d279208 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d263731, d279208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263731, d279208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d5238 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h8 (q : Pattern) (ha : d5239 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5243 q = 1) (hb : d69327 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5243, d69327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5243, d69327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2061 q = 1) (hb : d53340 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5244 q = 1) (hb : d69328 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5244, d69328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5244, d69328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5245 q = 1) (hb : d69329 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, d69329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5245, d69329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d263732 q = 1) (hb : d279209 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d263732, d279209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263732, d279209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro70269 (p : Pattern) (ha : d263738 p = 1) (hb : d279231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263611 q = 1) (hb : d279220 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263611, d279220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70244 q ha hb
    | true =>
      simp only [d263611, d279220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263612 q = 1) (hb : d279221 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263612, d279221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263612, d279221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263613 q = 1) (hb : d279222 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263613, d279222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263613, d279222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263614 q = 1) (hb : d279223 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263614, d279223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263614, d279223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263616 q = 1) (hb : d279225 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263616, d279225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70245 q ha hb
    | true =>
      simp only [d263616, d279225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263617 q = 1) (hb : d279226 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263617, d279226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263617, d279226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263618 q = 1) (hb : d279227 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263618, d279227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263618, d279227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263619 q = 1) (hb : d279228 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263619, d279228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263619, d279228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263620 q = 1) (hb : d279229 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263620, d279229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263620, d279229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263733 q = 1) (hb : d279210 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263733, d279210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70268 q ha hb
    | true =>
      simp only [d263733, d279210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d263734 q = 1) (hb : d279211 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263734, d279211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263734, d279211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d263735 q = 1) (hb : d279212 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263735, d279212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263735, d279212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263736 q = 1) (hb : d279213 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263736, d279213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263736, d279213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d263737 q = 1) (hb : d279230 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263737, d279230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263737, d279230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d263738 q = 1) (hb : d279231 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263738, d279231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263738, d279231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro70270 (p : Pattern) (ha : d263744 p = 1) (hb : d279224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35362 q = 1) (hb : d263592 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35362, d263592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35362, d263592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70240 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d35363 q = 1) (hb : d263593 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35363, d263593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35363, d263593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d35644 q = 1) (hb : d263739 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35644, d263739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
    | true =>
      simp only [d35644, d263739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h5 (q : Pattern) (ha : d35645 q = 1) (hb : d263740 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35645, d263740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d35645, d263740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d263741 q = 1) (hb : d279216 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d263741, d279216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d263741, d279216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d2029 q = 1) (hb : d53308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2030 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2049 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d263742 q = 1) (hb : d279217 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d263742, d279217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263742, d279217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d263743 q = 1) (hb : d279218 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d263743, d279218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263743, d279218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d5238 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h15 (q : Pattern) (ha : d5239 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5243 q = 1) (hb : d69327 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5243, d69327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5243, d69327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d2061 q = 1) (hb : d53340 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5244 q = 1) (hb : d69328 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5244, d69328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5244, d69328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5245 q = 1) (hb : d69329 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, d69329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5245, d69329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d263744 q = 1) (hb : d279224 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d263744, d279224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263744, d279224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  exact h20 p ha hb
theorem andIntro70271 (p : Pattern) (ha : d263750 p = 1) (hb : d279334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263745 q = 1) (hb : d279225 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263745, d279225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70270 q ha hb
    | true =>
      simp only [d263745, d279225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263746 q = 1) (hb : d279226 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263746, d279226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263746, d279226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263747 q = 1) (hb : d279227 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263747, d279227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263747, d279227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263748 q = 1) (hb : d279228 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263748, d279228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263748, d279228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263749 q = 1) (hb : d279249 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263749, d279249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263749, d279249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263750 q = 1) (hb : d279334 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263750, d279334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263750, d279334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70272 (p : Pattern) (ha : d263756 p = 1) (hb : d279340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263623 q = 1) (hb : d279232 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263623, d279232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70242 q ha hb
    | true =>
      simp only [d263623, d279232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70246 q ha hb
  have h2 (q : Pattern) (ha : d263624 q = 1) (hb : d279233 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263624, d279233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263624, d279233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263625 q = 1) (hb : d279234 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263625, d279234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263625, d279234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263638 q = 1) (hb : d279245 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263638, d279245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70246 q ha hb
    | true =>
      simp only [d263638, d279245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70249 q ha hb
  have h5 (q : Pattern) (ha : d263639 q = 1) (hb : d279246 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263639, d279246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263639, d279246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263640 q = 1) (hb : d279247 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263640, d279247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263640, d279247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263641 q = 1) (hb : d279248 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263641, d279248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263641, d279248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263751 q = 1) (hb : d279335 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263751, d279335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70269 q ha hb
    | true =>
      simp only [d263751, d279335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70271 q ha hb
  have h9 (q : Pattern) (ha : d263752 q = 1) (hb : d279336 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263752, d279336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263752, d279336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263753 q = 1) (hb : d279337 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263753, d279337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263753, d279337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263754 q = 1) (hb : d279338 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263754, d279338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263754, d279338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d263755 q = 1) (hb : d279339 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263755, d279339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263755, d279339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263756 q = 1) (hb : d279340 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263756, d279340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263756, d279340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro70273 (p : Pattern) (ha : d263762 p = 1) (hb : d279346 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263757 q = 1) (hb : d279341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263757, d279341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70272 q ha hb
    | true =>
      simp only [d263757, d279341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263758 q = 1) (hb : d279342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263758, d279342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263758, d279342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263759 q = 1) (hb : d279343 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263759, d279343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263759, d279343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263760 q = 1) (hb : d279344 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263760, d279344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263760, d279344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263761 q = 1) (hb : d279345 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263761, d279345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263761, d279345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263762 q = 1) (hb : d279346 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263762, d279346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263762, d279346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70274 (p : Pattern) (ha : d263768 p = 1) (hb : d279352 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263687 q = 1) (hb : d279294 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263687, d279294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70259 q ha hb
    | true =>
      simp only [d263687, d279294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70260 q ha hb
  have h2 (q : Pattern) (ha : d263688 q = 1) (hb : d279295 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263688, d279295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263688, d279295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263689 q = 1) (hb : d279296 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263689, d279296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263689, d279296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263690 q = 1) (hb : d279297 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263690, d279297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263690, d279297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263697 q = 1) (hb : d279304 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263697, d279304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70261 q ha hb
    | true =>
      simp only [d263697, d279304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70262 q ha hb
  have h6 (q : Pattern) (ha : d263698 q = 1) (hb : d279305 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263698, d279305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263698, d279305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263699 q = 1) (hb : d279306 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263699, d279306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263699, d279306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263727 q = 1) (hb : d279332 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263727, d279332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70266 q ha hb
    | true =>
      simp only [d263727, d279332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70267 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d263664 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d263728 q = 1) (hb : d279333 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263728, d279333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263728, d279333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d263763 q = 1) (hb : d279347 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263763, d279347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70273 q ha hb
    | true =>
      simp only [d263763, d279347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d263764 q = 1) (hb : d279348 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263764, d279348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263764, d279348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d263765 q = 1) (hb : d279349 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263765, d279349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263765, d279349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263766 q = 1) (hb : d279350 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263766, d279350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263766, d279350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d263767 q = 1) (hb : d279351 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263767, d279351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263767, d279351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d263768 q = 1) (hb : d279352 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263768, d279352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263768, d279352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro70275 (p : Pattern) (ha : d263769 p = 1) (hb : d279353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263650 q = 1) (hb : d279257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263650, d279257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70251 q ha hb
    | true =>
      simp only [d263650, d279257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263651 q = 1) (hb : d279258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263651, d279258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263651, d279258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263654 q = 1) (hb : d279261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70252 q ha hb
    | true =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263655 q = 1) (hb : d279262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263656 q = 1) (hb : d279263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263656, d279263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263656, d279263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263657 q = 1) (hb : d279264 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263657, d279264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263657, d279264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263683 q = 1) (hb : d279290 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263683, d279290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263683, d279290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263769 q = 1) (hb : d279353 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263769, d279353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263769, d279353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro70276 (p : Pattern) (ha : d263770 p = 1) (hb : d279354 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263654 q = 1) (hb : d279261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70252 q ha hb
    | true =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263655 q = 1) (hb : d279262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263660 q = 1) (hb : d279267 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263660, d279267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263660, d279267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263661 q = 1) (hb : d279268 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263661, d279268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263661, d279268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263685 q = 1) (hb : d279292 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263685, d279292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263685, d279292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263770 q = 1) (hb : d279354 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263770, d279354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263770, d279354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70277 (p : Pattern) (ha : d263775 p = 1) (hb : d279359 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263650 q = 1) (hb : d279257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263650, d279257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70251 q ha hb
    | true =>
      simp only [d263650, d279257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263651 q = 1) (hb : d279258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263651, d279258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263651, d279258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263654 q = 1) (hb : d279261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70252 q ha hb
    | true =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263655 q = 1) (hb : d279262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263656 q = 1) (hb : d279263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263656, d279263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263656, d279263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263691 q = 1) (hb : d279298 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263691, d279298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263691, d279298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263692 q = 1) (hb : d279299 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263692, d279299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263692, d279299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263775 q = 1) (hb : d279359 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263775, d279359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263775, d279359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro70278 (p : Pattern) (ha : d263776 p = 1) (hb : d279360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263654 q = 1) (hb : d279261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70252 q ha hb
    | true =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263655 q = 1) (hb : d279262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263660 q = 1) (hb : d279267 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263660, d279267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263660, d279267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263694 q = 1) (hb : d279301 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263694, d279301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263694, d279301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263695 q = 1) (hb : d279302 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263695, d279302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263695, d279302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263776 q = 1) (hb : d279360 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263776, d279360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263776, d279360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70279 (p : Pattern) (ha : d263780 p = 1) (hb : d279364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263712 q = 1) (hb : d279317 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263712, d279317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70264 q ha hb
    | true =>
      simp only [d263712, d279317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263713 q = 1) (hb : d279318 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263713, d279318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263713, d279318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263717 q = 1) (hb : d279322 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263717, d279322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70265 q ha hb
    | true =>
      simp only [d263717, d279322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263718 q = 1) (hb : d279323 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263718, d279323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263718, d279323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263719 q = 1) (hb : d279324 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263719, d279324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263719, d279324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263720 q = 1) (hb : d279325 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263720, d279325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263720, d279325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263721 q = 1) (hb : d279326 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263721, d279326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263721, d279326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263780 q = 1) (hb : d279364 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263780, d279364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263780, d279364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro70280 (p : Pattern) (ha : d263781 p = 1) (hb : d279365 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263717 q = 1) (hb : d279322 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263717, d279322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70265 q ha hb
    | true =>
      simp only [d263717, d279322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263718 q = 1) (hb : d279323 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263718, d279323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263718, d279323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263654 q = 1) (hb : d279261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70252 q ha hb
    | true =>
      simp only [d263654, d279261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263655 q = 1) (hb : d279262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263655, d279262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263723 q = 1) (hb : d279328 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263723, d279328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263723, d279328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263724 q = 1) (hb : d279329 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263724, d279329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263724, d279329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263725 q = 1) (hb : d279330 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263725, d279330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263725, d279330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263781 q = 1) (hb : d279365 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263781, d279365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263781, d279365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro70281 (p : Pattern) (ha : d263784 p = 1) (hb : d279368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263757 q = 1) (hb : d279341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263757, d279341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70272 q ha hb
    | true =>
      simp only [d263757, d279341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263758 q = 1) (hb : d279342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263758, d279342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263758, d279342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263759 q = 1) (hb : d279343 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263759, d279343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263759, d279343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263760 q = 1) (hb : d279344 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263760, d279344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263760, d279344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263761 q = 1) (hb : d279345 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263761, d279345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263761, d279345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263784 q = 1) (hb : d279368 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263784, d279368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263784, d279368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70282 (p : Pattern) (ha : d263790 p = 1) (hb : d279374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263687 q = 1) (hb : d279294 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263687, d279294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70259 q ha hb
    | true =>
      simp only [d263687, d279294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70260 q ha hb
  have h2 (q : Pattern) (ha : d263688 q = 1) (hb : d279295 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263688, d279295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263688, d279295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263689 q = 1) (hb : d279296 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263689, d279296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263689, d279296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263690 q = 1) (hb : d279297 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263690, d279297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263690, d279297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263697 q = 1) (hb : d279304 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263697, d279304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70261 q ha hb
    | true =>
      simp only [d263697, d279304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70262 q ha hb
  have h6 (q : Pattern) (ha : d263698 q = 1) (hb : d279305 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263698, d279305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263698, d279305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263699 q = 1) (hb : d279306 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263699, d279306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263699, d279306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263727 q = 1) (hb : d279332 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263727, d279332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70266 q ha hb
    | true =>
      simp only [d263727, d279332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70267 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d263664 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d263728 q = 1) (hb : d279333 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263728, d279333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263728, d279333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d263763 q = 1) (hb : d279347 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263763, d279347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70273 q ha hb
    | true =>
      simp only [d263763, d279347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d263764 q = 1) (hb : d279348 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263764, d279348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263764, d279348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d263765 q = 1) (hb : d279349 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263765, d279349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263765, d279349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263766 q = 1) (hb : d279350 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263766, d279350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263766, d279350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d263767 q = 1) (hb : d279351 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263767, d279351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263767, d279351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d263771 q = 1) (hb : d279355 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263771, d279355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70275 q ha hb
    | true =>
      simp only [d263771, d279355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70276 q ha hb
  have h17 (q : Pattern) (ha : d263772 q = 1) (hb : d279356 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263772, d279356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263772, d279356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d263773 q = 1) (hb : d279357 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263773, d279357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263773, d279357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d263774 q = 1) (hb : d279358 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263774, d279358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263774, d279358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d263777 q = 1) (hb : d279361 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263777, d279361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70277 q ha hb
    | true =>
      simp only [d263777, d279361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70278 q ha hb
  have h21 (q : Pattern) (ha : d263778 q = 1) (hb : d279362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263778, d279362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263778, d279362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d263779 q = 1) (hb : d279363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263779, d279363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d263779, d279363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d263782 q = 1) (hb : d279366 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263782, d279366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70279 q ha hb
    | true =>
      simp only [d263782, d279366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70280 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d263674 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d263783 q = 1) (hb : d279367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263783, d279367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d263783, d279367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d263785 q = 1) (hb : d279369 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263785, d279369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70281 q ha hb
    | true =>
      simp only [d263785, d279369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d263786 q = 1) (hb : d279370 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263786, d279370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d263786, d279370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d263787 q = 1) (hb : d279371 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263787, d279371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d263787, d279371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d263788 q = 1) (hb : d279372 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263788, d279372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d263788, d279372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d263789 q = 1) (hb : d279373 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263789, d279373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d263789, d279373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d263790 q = 1) (hb : d279374 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263790, d279374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263790, d279374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro70283 (p : Pattern) (ha : d263802 p = 1) (hb : d279386 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263792 q = 1) (hb : d279376 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263792, d279376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70267 q ha hb
    | true =>
      simp only [d263792, d279376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70254 q ha hb
  have h2 (q : Pattern) (ha : d263793 q = 1) (hb : d279377 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263793, d279377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263793, d279377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263794 q = 1) (hb : d279378 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263794, d279378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263794, d279378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263795 q = 1) (hb : d279379 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263795, d279379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263795, d279379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263796 q = 1) (hb : d279380 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263796, d279380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263796, d279380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263797 q = 1) (hb : d279381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263797, d279381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70254 q ha hb
    | true =>
      simp only [d263797, d279381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263798 q = 1) (hb : d279382 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263798, d279382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263798, d279382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263799 q = 1) (hb : d279383 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263799, d279383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263799, d279383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263800 q = 1) (hb : d279384 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263800, d279384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263800, d279384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263801 q = 1) (hb : d279385 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263801, d279385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263801, d279385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263802 q = 1) (hb : d279386 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263802, d279386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263802, d279386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro70284 (p : Pattern) (ha : d263808 p = 1) (hb : d279392 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263797 q = 1) (hb : d279381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263797, d279381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70254 q ha hb
    | true =>
      simp only [d263797, d279381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263798 q = 1) (hb : d279382 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263798, d279382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263798, d279382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263799 q = 1) (hb : d279383 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263799, d279383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263799, d279383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263800 q = 1) (hb : d279384 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263800, d279384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263800, d279384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263801 q = 1) (hb : d279385 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263801, d279385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263801, d279385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263803 q = 1) (hb : d279387 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263803, d279387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70257 q ha hb
    | true =>
      simp only [d263803, d279387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263804 q = 1) (hb : d279388 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263804, d279388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263804, d279388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263805 q = 1) (hb : d279389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263805, d279389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263805, d279389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263806 q = 1) (hb : d279390 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263806, d279390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263806, d279390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263807 q = 1) (hb : d279391 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263807, d279391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263807, d279391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263808 q = 1) (hb : d279392 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263808, d279392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263808, d279392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro70285 (p : Pattern) (ha : d263815 p = 1) (hb : d279399 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263782 q = 1) (hb : d279366 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263782, d279366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70279 q ha hb
    | true =>
      simp only [d263782, d279366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70280 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263674 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263783 q = 1) (hb : d279367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263783, d279367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263783, d279367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d263785 q = 1) (hb : d279369 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263785, d279369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70281 q ha hb
    | true =>
      simp only [d263785, d279369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263786 q = 1) (hb : d279370 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263786, d279370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263786, d279370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263787 q = 1) (hb : d279371 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263787, d279371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263787, d279371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263813 q = 1) (hb : d279397 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263813, d279397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263813, d279397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263814 q = 1) (hb : d279398 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263814, d279398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263814, d279398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263815 q = 1) (hb : d279399 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263815, d279399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263815, d279399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro70286 (p : Pattern) (ha : d263817 p = 1) (hb : d279401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263803 q = 1) (hb : d279387 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263803, d279387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70257 q ha hb
    | true =>
      simp only [d263803, d279387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263804 q = 1) (hb : d279388 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263804, d279388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263804, d279388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263805 q = 1) (hb : d279389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263805, d279389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263805, d279389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263806 q = 1) (hb : d279390 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263806, d279390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263806, d279390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263807 q = 1) (hb : d279391 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263807, d279391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263807, d279391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263817 q = 1) (hb : d279401 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263817, d279401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263817, d279401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70287 (p : Pattern) (ha : d263843 p = 1) (hb : d279417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35737 q = 1) (hb : d263829 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d35737, d263829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35737, d263829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70238 q ha hb
  have h2 (q : Pattern) (ha : d35368 q = 1) (hb : d263567 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d35368, d263567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70238 q ha hb
    | true =>
      simp only [d35368, d263567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d35738 q = 1) (hb : d263830 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d35738, d263830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35738, d263830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d35369 q = 1) (hb : d263568 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d35369, d263568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d35369, d263568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d35739 q = 1) (hb : d263831 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d35739, d263831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d35739, d263831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d35740 q = 1) (hb : d263832 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d35740, d263832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d35740, d263832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d263833 q = 1) (hb : d279407 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263833, d279407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263833, d279407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70239 q ha hb
  have h8 (q : Pattern) (ha : d263581 q = 1) (hb : d279201 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263581, d279201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70239 q ha hb
    | true =>
      simp only [d263581, d279201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263834 q = 1) (hb : d279408 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263834, d279408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263834, d279408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263582 q = 1) (hb : d279202 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263582, d279202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263582, d279202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d263835 q = 1) (hb : d279409 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263835, d279409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263835, d279409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d263836 q = 1) (hb : d279410 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263836, d279410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263836, d279410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d263837 q = 1) (hb : d279411 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263837, d279411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d263837, d279411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263826 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263838 q = 1) (hb : d279412 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263838, d279412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263838, d279412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70241 q ha hb
  have h16 (q : Pattern) (ha : d263598 q = 1) (hb : d279210 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263598, d279210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70241 q ha hb
    | true =>
      simp only [d263598, d279210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d263839 q = 1) (hb : d279413 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263839, d279413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263839, d279413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d263599 q = 1) (hb : d279211 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263599, d279211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263599, d279211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d263840 q = 1) (hb : d279414 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263840, d279414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263840, d279414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d263841 q = 1) (hb : d279415 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263841, d279415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d263841, d279415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d263842 q = 1) (hb : d279416 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263842, d279416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d263842, d279416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d263843 q = 1) (hb : d279417 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263843, d279417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263843, d279417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro70288 (p : Pattern) (ha : d263848 p = 1) (hb : d279422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263826 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263838 q = 1) (hb : d279412 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263838, d279412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263838, d279412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70241 q ha hb
  have h3 (q : Pattern) (ha : d263598 q = 1) (hb : d279210 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263598, d279210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70241 q ha hb
    | true =>
      simp only [d263598, d279210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d263839 q = 1) (hb : d279413 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263839, d279413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263839, d279413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263599 q = 1) (hb : d279211 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263599, d279211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263599, d279211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d263840 q = 1) (hb : d279414 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263840, d279414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263840, d279414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263841 q = 1) (hb : d279415 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263841, d279415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263841, d279415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d263842 q = 1) (hb : d279416 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263842, d279416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263842, d279416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263847 q = 1) (hb : d279421 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263847, d279421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263847, d279421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h10 (q : Pattern) (ha : d263848 q = 1) (hb : d279422 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263848, d279422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263848, d279422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro70289 (p : Pattern) (ha : d263862 p = 1) (hb : d279436 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263853 q = 1) (hb : d279427 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263853, d279427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263853, d279427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70244 q ha hb
  have h2 (q : Pattern) (ha : d263611 q = 1) (hb : d279220 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263611, d279220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70244 q ha hb
    | true =>
      simp only [d263611, d279220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263854 q = 1) (hb : d279428 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263854, d279428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263854, d279428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263612 q = 1) (hb : d279221 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263612, d279221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263612, d279221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263855 q = 1) (hb : d279429 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263855, d279429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263855, d279429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263856 q = 1) (hb : d279430 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263856, d279430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263856, d279430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263857 q = 1) (hb : d279431 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263857, d279431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263857, d279431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70245 q ha hb
  have h8 (q : Pattern) (ha : d263616 q = 1) (hb : d279225 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263616, d279225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70245 q ha hb
    | true =>
      simp only [d263616, d279225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263858 q = 1) (hb : d279432 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263858, d279432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263858, d279432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263617 q = 1) (hb : d279226 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263617, d279226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263617, d279226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d263859 q = 1) (hb : d279433 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263859, d279433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263859, d279433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d263860 q = 1) (hb : d279434 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263860, d279434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263860, d279434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d263861 q = 1) (hb : d279435 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263861, d279435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263861, d279435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263838 q = 1) (hb : d279412 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263838, d279412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263838, d279412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70241 q ha hb
  have h15 (q : Pattern) (ha : d263598 q = 1) (hb : d279210 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263598, d279210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70241 q ha hb
    | true =>
      simp only [d263598, d279210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d263839 q = 1) (hb : d279413 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263839, d279413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d263839, d279413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d263599 q = 1) (hb : d279211 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263599, d279211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263599, d279211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d263840 q = 1) (hb : d279414 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263840, d279414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263840, d279414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d263841 q = 1) (hb : d279415 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263841, d279415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d263841, d279415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d263847 q = 1) (hb : d279421 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263847, d279421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d263847, d279421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d263862 q = 1) (hb : d279436 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263862, d279436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263862, d279436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro70290 (p : Pattern) (ha : d263871 p = 1) (hb : d279445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263866 q = 1) (hb : d279440 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263866, d279440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263866, d279440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70248 q ha hb
  have h2 (q : Pattern) (ha : d263632 q = 1) (hb : d279239 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263632, d279239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70248 q ha hb
    | true =>
      simp only [d263632, d279239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263867 q = 1) (hb : d279441 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263867, d279441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263867, d279441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263633 q = 1) (hb : d279240 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263633, d279240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263633, d279240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263868 q = 1) (hb : d279442 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263868, d279442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263868, d279442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263869 q = 1) (hb : d279443 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263869, d279443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263869, d279443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263870 q = 1) (hb : d279444 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263870, d279444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263870, d279444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123743 q = 1) (hb : d270722 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d123743, d270722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123743, d270722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70247 q ha hb
  have h9 (q : Pattern) (ha : d101733 q = 1) (hb : d270516 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d101733, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70247 q ha hb
    | true =>
      simp only [d101733, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123744 q = 1) (hb : d270723 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d123744, d270723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123744, d270723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d101735 q = 1) (hb : d270517 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d101735, d270517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d101735, d270517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123745 q = 1) (hb : d270724 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123745, d270724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123745, d270724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123746 q = 1) (hb : d270725 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123746, d270725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123746, d270725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d123747 q = 1) (hb : d270726 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123747, d270726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123747, d270726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d263871 q = 1) (hb : d279445 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263871, d279445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263871, d279445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro70291 (p : Pattern) (ha : d263877 p = 1) (hb : d279451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263828 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263844 q = 1) (hb : d279418 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263844, d279418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263844, d279418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70287 q ha hb
  have h3 (q : Pattern) (ha : d263845 q = 1) (hb : d279419 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263845, d279419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263845, d279419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263846 q = 1) (hb : d279420 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263846, d279420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263846, d279420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263849 q = 1) (hb : d279423 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263849, d279423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70287 q ha hb
    | true =>
      simp only [d263849, d279423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70288 q ha hb
  have h6 (q : Pattern) (ha : d263850 q = 1) (hb : d279424 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263850, d279424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263850, d279424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263851 q = 1) (hb : d279425 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263851, d279425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263851, d279425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263852 q = 1) (hb : d279426 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263852, d279426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263852, d279426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263863 q = 1) (hb : d279437 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263863, d279437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70287 q ha hb
    | true =>
      simp only [d263863, d279437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70289 q ha hb
  have h10 (q : Pattern) (ha : d263864 q = 1) (hb : d279438 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263864, d279438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263864, d279438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263865 q = 1) (hb : d279439 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263865, d279439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263865, d279439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d263872 q = 1) (hb : d279446 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263872, d279446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70289 q ha hb
    | true =>
      simp only [d263872, d279446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70290 q ha hb
  have h13 (q : Pattern) (ha : d263873 q = 1) (hb : d279447 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263873, d279447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263873, d279447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263874 q = 1) (hb : d279448 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263874, d279448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263874, d279448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d263875 q = 1) (hb : d279449 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263875, d279449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263875, d279449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d263876 q = 1) (hb : d279450 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263876, d279450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263876, d279450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d263877 q = 1) (hb : d279451 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263877, d279451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263877, d279451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro70292 (p : Pattern) (ha : d263882 p = 1) (hb : d279456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263863 q = 1) (hb : d279437 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263863, d279437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70287 q ha hb
    | true =>
      simp only [d263863, d279437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70289 q ha hb
  have h2 (q : Pattern) (ha : d263864 q = 1) (hb : d279438 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263864, d279438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263864, d279438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263865 q = 1) (hb : d279439 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263865, d279439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263865, d279439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263872 q = 1) (hb : d279446 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263872, d279446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70289 q ha hb
    | true =>
      simp only [d263872, d279446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70290 q ha hb
  have h5 (q : Pattern) (ha : d263873 q = 1) (hb : d279447 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263873, d279447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263873, d279447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263874 q = 1) (hb : d279448 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263874, d279448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263874, d279448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263875 q = 1) (hb : d279449 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263875, d279449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263875, d279449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263880 q = 1) (hb : d279454 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263880, d279454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263880, d279454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263881 q = 1) (hb : d279455 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263881, d279455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263881, d279455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263882 q = 1) (hb : d279456 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263882, d279456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263882, d279456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro70293 (p : Pattern) (ha : d263888 p = 1) (hb : d279462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263878 q = 1) (hb : d279452 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263878, d279452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70291 q ha hb
    | true =>
      simp only [d263878, d279452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263879 q = 1) (hb : d279453 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263879, d279453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263879, d279453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263883 q = 1) (hb : d279457 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263883, d279457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70292 q ha hb
    | true =>
      simp only [d263883, d279457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263884 q = 1) (hb : d279458 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263884, d279458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263884, d279458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263885 q = 1) (hb : d279459 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263885, d279459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263885, d279459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263886 q = 1) (hb : d279460 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263886, d279460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263886, d279460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263887 q = 1) (hb : d279461 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263887, d279461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263887, d279461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263888 q = 1) (hb : d279462 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263888, d279462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263888, d279462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro70294 (p : Pattern) (ha : d263890 p = 1) (hb : d279464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263857 q = 1) (hb : d279431 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263857, d279431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263857, d279431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70245 q ha hb
  have h2 (q : Pattern) (ha : d263616 q = 1) (hb : d279225 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263616, d279225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70245 q ha hb
    | true =>
      simp only [d263616, d279225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263858 q = 1) (hb : d279432 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263858, d279432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263858, d279432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263617 q = 1) (hb : d279226 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263617, d279226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263617, d279226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263859 q = 1) (hb : d279433 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263859, d279433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263859, d279433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263860 q = 1) (hb : d279434 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263860, d279434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263860, d279434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263889 q = 1) (hb : d279463 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263889, d279463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263889, d279463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123743 q = 1) (hb : d270722 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d123743, d270722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123743, d270722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70247 q ha hb
  have h9 (q : Pattern) (ha : d101733 q = 1) (hb : d270516 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d101733, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70247 q ha hb
    | true =>
      simp only [d101733, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123744 q = 1) (hb : d270723 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d123744, d270723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123744, d270723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d101735 q = 1) (hb : d270517 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d101735, d270517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d101735, d270517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123745 q = 1) (hb : d270724 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123745, d270724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123745, d270724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123746 q = 1) (hb : d270725 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123746, d270725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123746, d270725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d123747 q = 1) (hb : d270726 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123747, d270726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123747, d270726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d263890 q = 1) (hb : d279464 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263890, d279464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263890, d279464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro70295 (p : Pattern) (ha : d263896 p = 1) (hb : d279470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263891 q = 1) (hb : d279465 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263891, d279465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70289 q ha hb
    | true =>
      simp only [d263891, d279465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70294 q ha hb
  have h2 (q : Pattern) (ha : d263892 q = 1) (hb : d279466 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263892, d279466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263892, d279466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263893 q = 1) (hb : d279467 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263893, d279467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263893, d279467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263894 q = 1) (hb : d279468 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263894, d279468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263894, d279468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263895 q = 1) (hb : d279469 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263895, d279469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263895, d279469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263896 q = 1) (hb : d279470 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263896, d279470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263896, d279470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70296 (p : Pattern) (ha : d263902 p = 1) (hb : d279476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263883 q = 1) (hb : d279457 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263883, d279457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70292 q ha hb
    | true =>
      simp only [d263883, d279457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263884 q = 1) (hb : d279458 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263884, d279458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263884, d279458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263897 q = 1) (hb : d279471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263897, d279471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70295 q ha hb
    | true =>
      simp only [d263897, d279471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263898 q = 1) (hb : d279472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263898, d279472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263898, d279472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263899 q = 1) (hb : d279473 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263899, d279473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263899, d279473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263900 q = 1) (hb : d279474 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263900, d279474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263900, d279474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263901 q = 1) (hb : d279475 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263901, d279475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263901, d279475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263902 q = 1) (hb : d279476 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263902, d279476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263902, d279476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro70297 (p : Pattern) (ha : d263948 p = 1) (hb : d279436 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263853 q = 1) (hb : d279427 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263853, d279427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263853, d279427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70244 q ha hb
  have h2 (q : Pattern) (ha : d263611 q = 1) (hb : d279220 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263611, d279220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70244 q ha hb
    | true =>
      simp only [d263611, d279220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263854 q = 1) (hb : d279428 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263854, d279428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263854, d279428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263612 q = 1) (hb : d279221 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263612, d279221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263612, d279221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263855 q = 1) (hb : d279429 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263855, d279429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263855, d279429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263856 q = 1) (hb : d279430 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263856, d279430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263856, d279430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263857 q = 1) (hb : d279431 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263857, d279431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263857, d279431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70245 q ha hb
  have h8 (q : Pattern) (ha : d263616 q = 1) (hb : d279225 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263616, d279225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70245 q ha hb
    | true =>
      simp only [d263616, d279225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d263858 q = 1) (hb : d279432 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263858, d279432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263858, d279432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263617 q = 1) (hb : d279226 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263617, d279226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263617, d279226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d263859 q = 1) (hb : d279433 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263859, d279433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263859, d279433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d263860 q = 1) (hb : d279434 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263860, d279434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263860, d279434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d263861 q = 1) (hb : d279435 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263861, d279435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263861, d279435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263943 q = 1) (hb : d279412 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263943, d279412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263943, d279412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70268 q ha hb
  have h15 (q : Pattern) (ha : d263733 q = 1) (hb : d279210 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263733, d279210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70268 q ha hb
    | true =>
      simp only [d263733, d279210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d263944 q = 1) (hb : d279413 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263944, d279413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d263944, d279413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d263734 q = 1) (hb : d279211 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263734, d279211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263734, d279211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d263945 q = 1) (hb : d279414 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263945, d279414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263945, d279414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d263946 q = 1) (hb : d279415 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263946, d279415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d263946, d279415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d263947 q = 1) (hb : d279421 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263947, d279421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d263947, d279421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d263948 q = 1) (hb : d279436 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263948, d279436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263948, d279436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro70298 (p : Pattern) (ha : d263954 p = 1) (hb : d279479 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263949 q = 1) (hb : d279431 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263949, d279431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263949, d279431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70270 q ha hb
  have h2 (q : Pattern) (ha : d263745 q = 1) (hb : d279225 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263745, d279225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70270 q ha hb
    | true =>
      simp only [d263745, d279225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263950 q = 1) (hb : d279432 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263950, d279432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263950, d279432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263746 q = 1) (hb : d279226 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263746, d279226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263746, d279226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263951 q = 1) (hb : d279433 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263951, d279433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263951, d279433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263952 q = 1) (hb : d279434 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263952, d279434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263952, d279434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263953 q = 1) (hb : d279463 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263953, d279463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263953, d279463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263954 q = 1) (hb : d279479 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263954, d279479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263954, d279479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro70299 (p : Pattern) (ha : d263960 p = 1) (hb : d279485 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263863 q = 1) (hb : d279437 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263863, d279437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70287 q ha hb
    | true =>
      simp only [d263863, d279437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70289 q ha hb
  have h2 (q : Pattern) (ha : d263864 q = 1) (hb : d279438 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263864, d279438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263864, d279438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263865 q = 1) (hb : d279439 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263865, d279439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263865, d279439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263872 q = 1) (hb : d279446 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263872, d279446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70289 q ha hb
    | true =>
      simp only [d263872, d279446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70290 q ha hb
  have h5 (q : Pattern) (ha : d263873 q = 1) (hb : d279447 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263873, d279447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263873, d279447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263874 q = 1) (hb : d279448 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263874, d279448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263874, d279448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263875 q = 1) (hb : d279449 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263875, d279449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263875, d279449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263955 q = 1) (hb : d279480 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263955, d279480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70297 q ha hb
    | true =>
      simp only [d263955, d279480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70298 q ha hb
  have h9 (q : Pattern) (ha : d263956 q = 1) (hb : d279481 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263956, d279481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263956, d279481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263957 q = 1) (hb : d279482 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263957, d279482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263957, d279482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263958 q = 1) (hb : d279483 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263958, d279483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263958, d279483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d263959 q = 1) (hb : d279484 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263959, d279484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263959, d279484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263960 q = 1) (hb : d279485 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263960, d279485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263960, d279485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro70300 (p : Pattern) (ha : d263966 p = 1) (hb : d279491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263961 q = 1) (hb : d279486 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263961, d279486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70299 q ha hb
    | true =>
      simp only [d263961, d279486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263962 q = 1) (hb : d279487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263962, d279487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263962, d279487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263963 q = 1) (hb : d279488 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263963, d279488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263963, d279488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263964 q = 1) (hb : d279489 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263964, d279489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263964, d279489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263965 q = 1) (hb : d279490 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263965, d279490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263965, d279490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263966 q = 1) (hb : d279491 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263966, d279491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263966, d279491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70301 (p : Pattern) (ha : d263972 p = 1) (hb : d279497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263903 q = 1) (hb : d279477 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263903, d279477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70293 q ha hb
    | true =>
      simp only [d263903, d279477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70296 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263941 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263942 q = 1) (hb : d279478 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263942, d279478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263942, d279478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d263967 q = 1) (hb : d279492 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263967, d279492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70300 q ha hb
    | true =>
      simp only [d263967, d279492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263968 q = 1) (hb : d279493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263968, d279493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263968, d279493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263969 q = 1) (hb : d279494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263969, d279494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263969, d279494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263970 q = 1) (hb : d279495 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263970, d279495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263970, d279495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263971 q = 1) (hb : d279496 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263971, d279496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263971, d279496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263972 q = 1) (hb : d279497 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263972, d279497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263972, d279497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro70302 (p : Pattern) (ha : d263977 p = 1) (hb : d279502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263897 q = 1) (hb : d279471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263897, d279471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70295 q ha hb
    | true =>
      simp only [d263897, d279471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263898 q = 1) (hb : d279472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263898, d279472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263898, d279472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263974 q = 1) (hb : d279499 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263974, d279499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263974, d279499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263975 q = 1) (hb : d279500 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263975, d279500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263975, d279500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263976 q = 1) (hb : d279501 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263976, d279501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263976, d279501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263977 q = 1) (hb : d279502 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263977, d279502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263977, d279502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70303 (p : Pattern) (ha : d263983 p = 1) (hb : d279508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263978 q = 1) (hb : d279503 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263978, d279503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70302 q ha hb
    | true =>
      simp only [d263978, d279503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263979 q = 1) (hb : d279504 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263979, d279504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263979, d279504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263980 q = 1) (hb : d279505 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263980, d279505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263980, d279505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263981 q = 1) (hb : d279506 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263981, d279506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263981, d279506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263982 q = 1) (hb : d279507 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263982, d279507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263982, d279507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263983 q = 1) (hb : d279508 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263983, d279508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263983, d279508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70304 (p : Pattern) (ha : d263989 p = 1) (hb : d279514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263670 q = 1) (hb : d279277 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263670, d279277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263670, d279277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70255 q ha hb
  have h2 (q : Pattern) (ha : d263671 q = 1) (hb : d279278 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263671, d279278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263671, d279278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263680 q = 1) (hb : d279287 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263680, d279287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70255 q ha hb
    | true =>
      simp only [d263680, d279287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70258 q ha hb
  have h4 (q : Pattern) (ha : d263681 q = 1) (hb : d279288 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263681, d279288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263681, d279288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263682 q = 1) (hb : d279289 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263682, d279289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263682, d279289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263791 q = 1) (hb : d279375 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263791, d279375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70274 q ha hb
    | true =>
      simp only [d263791, d279375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70282 q ha hb
  have h7 (q : Pattern) (ha : d263809 q = 1) (hb : d279393 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263809, d279393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70283 q ha hb
    | true =>
      simp only [d263809, d279393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70284 q ha hb
  have h8 (q : Pattern) (ha : d263810 q = 1) (hb : d279394 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263810, d279394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263810, d279394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263811 q = 1) (hb : d279395 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263811, d279395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263811, d279395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d263812 q = 1) (hb : d279396 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263812, d279396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263812, d279396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263816 q = 1) (hb : d279400 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263816, d279400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263816, d279400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70285 q ha hb
  have h12 (q : Pattern) (ha : d263818 q = 1) (hb : d279402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263818, d279402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263818, d279402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70286 q ha hb
  have h13 (q : Pattern) (ha : d263819 q = 1) (hb : d279403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263819, d279403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263819, d279403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263820 q = 1) (hb : d279404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263820, d279404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263820, d279404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d263821 q = 1) (hb : d279405 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263821, d279405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d263821, d279405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d263822 q = 1) (hb : d279406 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263822, d279406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263822, d279406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d263973 q = 1) (hb : d279498 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263973, d279498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263973, d279498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70301 q ha hb
  have h18 (q : Pattern) (ha : d263984 q = 1) (hb : d279509 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263984, d279509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263984, d279509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70303 q ha hb
  have h19 (q : Pattern) (ha : d263985 q = 1) (hb : d279510 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263985, d279510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263985, d279510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d263986 q = 1) (hb : d279511 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263986, d279511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d263986, d279511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d263987 q = 1) (hb : d279512 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263987, d279512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d263987, d279512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d263988 q = 1) (hb : d279513 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263988, d279513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d263988, d279513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d263989 q = 1) (hb : d279514 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d263989, d279514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263989, d279514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro70305 (p : Pattern) (ha : d263995 p = 1) (hb : d279520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263990 q = 1) (hb : d279515 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d263990, d279515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263990, d279515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70304 q ha hb
  have h2 (q : Pattern) (ha : d263991 q = 1) (hb : d279516 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d263991, d279516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263991, d279516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263992 q = 1) (hb : d279517 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d263992, d279517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263992, d279517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263993 q = 1) (hb : d279518 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d263993, d279518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263993, d279518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263994 q = 1) (hb : d279519 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d263994, d279519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263994, d279519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263995 q = 1) (hb : d279520 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d263995, d279520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263995, d279520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70306 (p : Pattern) (ha : d264001 p = 1) (hb : d279526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d262468 q = 1) (hb : d278209 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d262468, d278209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70003 q ha hb
    | true =>
      simp only [d262468, d278209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70050 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262753 q = 1) (hb : d278479 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d262753, d278479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262753, d278479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70105 q ha hb
  have h3 (q : Pattern) (ha : d262754 q = 1) (hb : d278480 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d262754, d278480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d262754, d278480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263147 q = 1) (hb : d278853 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d263147, d278853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263147, d278853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70168 q ha hb
  have h5 (q : Pattern) (ha : d263148 q = 1) (hb : d278854 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d263148, d278854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263148, d278854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263149 q = 1) (hb : d278855 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d263149, d278855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263149, d278855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263557 q = 1) (hb : d279196 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d263557, d279196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263557, d279196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70237 q ha hb
  have h8 (q : Pattern) (ha : d263558 q = 1) (hb : d279197 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d263558, d279197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263558, d279197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263559 q = 1) (hb : d279198 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d263559, d279198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263559, d279198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263560 q = 1) (hb : d279199 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d263560, d279199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263560, d279199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263996 q = 1) (hb : d279521 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d263996, d279521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263996, d279521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70305 q ha hb
  have h12 (q : Pattern) (ha : d263997 q = 1) (hb : d279522 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d263997, d279522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263997, d279522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263998 q = 1) (hb : d279523 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d263998, d279523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263998, d279523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263999 q = 1) (hb : d279524 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d263999, d279524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263999, d279524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d264000 q = 1) (hb : d279525 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d264000, d279525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d264000, d279525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d264001 q = 1) (hb : d279526 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d264001, d279526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d264001, d279526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro70307 (p : Pattern) (ha : d264007 p = 1) (hb : d279532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264002 q = 1) (hb : d279527 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d264002, d279527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70306 q ha hb
    | true =>
      simp only [d264002, d279527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264003 q = 1) (hb : d279528 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d264003, d279528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264003, d279528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264004 q = 1) (hb : d279529 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d264004, d279529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264004, d279529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264005 q = 1) (hb : d279530 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d264005, d279530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264005, d279530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264006 q = 1) (hb : d279531 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d264006, d279531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264006, d279531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264007 q = 1) (hb : d279532 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d264007, d279532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264007, d279532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70308 (p : Pattern) (ha : d264013 p = 1) (hb : d279538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264008 q = 1) (hb : d279533 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d264008, d279533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70307 q ha hb
    | true =>
      simp only [d264008, d279533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264009 q = 1) (hb : d279534 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d264009, d279534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264009, d279534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264010 q = 1) (hb : d279535 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d264010, d279535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264010, d279535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264011 q = 1) (hb : d279536 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d264011, d279536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264011, d279536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264012 q = 1) (hb : d279537 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d264012, d279537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264012, d279537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264013 q = 1) (hb : d279538 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d264013, d279538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264013, d279538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70309 (p : Pattern) (ha : d264019 p = 1) (hb : d279544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264014 q = 1) (hb : d279539 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d264014, d279539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70308 q ha hb
    | true =>
      simp only [d264014, d279539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264015 q = 1) (hb : d279540 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d264015, d279540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264015, d279540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264016 q = 1) (hb : d279541 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d264016, d279541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264016, d279541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264017 q = 1) (hb : d279542 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d264017, d279542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264017, d279542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264018 q = 1) (hb : d279543 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d264018, d279543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264018, d279543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264019 q = 1) (hb : d279544 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d264019, d279544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264019, d279544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70310 (p : Pattern) (ha : d264025 p = 1) (hb : d279550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264020 q = 1) (hb : d279545 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d264020, d279545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70309 q ha hb
    | true =>
      simp only [d264020, d279545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264021 q = 1) (hb : d279546 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d264021, d279546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264021, d279546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264022 q = 1) (hb : d279547 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d264022, d279547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264022, d279547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264023 q = 1) (hb : d279548 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d264023, d279548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264023, d279548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264024 q = 1) (hb : d279549 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d264024, d279549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264024, d279549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264025 q = 1) (hb : d279550 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d264025, d279550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264025, d279550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70311 (p : Pattern) (ha : d264031 p = 1) (hb : d279556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264026 q = 1) (hb : d279551 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d264026, d279551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70310 q ha hb
    | true =>
      simp only [d264026, d279551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264027 q = 1) (hb : d279552 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d264027, d279552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264027, d279552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264028 q = 1) (hb : d279553 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d264028, d279553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264028, d279553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264029 q = 1) (hb : d279554 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d264029, d279554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264029, d279554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264030 q = 1) (hb : d279555 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d264030, d279555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264030, d279555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264031 q = 1) (hb : d279556 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d264031, d279556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264031, d279556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70312 (p : Pattern) (ha : d264037 p = 1) (hb : d279562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264032 q = 1) (hb : d279557 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d264032, d279557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70311 q ha hb
    | true =>
      simp only [d264032, d279557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264033 q = 1) (hb : d279558 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d264033, d279558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264033, d279558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264034 q = 1) (hb : d279559 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d264034, d279559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264034, d279559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264035 q = 1) (hb : d279560 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d264035, d279560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264035, d279560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264036 q = 1) (hb : d279561 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d264036, d279561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264036, d279561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264037 q = 1) (hb : d279562 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d264037, d279562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264037, d279562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70313 (p : Pattern) (ha : d264043 p = 1) (hb : d279568 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264038 q = 1) (hb : d279563 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d264038, d279563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70312 q ha hb
    | true =>
      simp only [d264038, d279563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264039 q = 1) (hb : d279564 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d264039, d279564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264039, d279564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264040 q = 1) (hb : d279565 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d264040, d279565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264040, d279565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264041 q = 1) (hb : d279566 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d264041, d279566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264041, d279566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264042 q = 1) (hb : d279567 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d264042, d279567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264042, d279567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264043 q = 1) (hb : d279568 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d264043, d279568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264043, d279568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70314 (p : Pattern) (ha : d53655 p = 1) (hb : d277740 p = 1) : d279571 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d277740 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d277740 q = 1) : d277773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69596 q ha hb
    | true =>
      simp only [d204, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287 q = 1) (hb : d277740 q = 1) : d277833 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d277833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d277833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288 q = 1) (hb : d277740 q = 1) : d277834 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d277834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288, d277834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d289 q = 1) (hb : d277740 q = 1) : d277835 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d277835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d277835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290 q = 1) (hb : d277740 q = 1) : d277836 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d277836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d277836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53655 q = 1) (hb : d277740 q = 1) : d279571 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d279571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d279571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro70315 (p : Pattern) (ha : d53665 p = 1) (hb : d277740 p = 1) : d279581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d277740 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d277740 q = 1) : d277809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d277809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69600 q ha hb
    | true =>
      simp only [d244, d277809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53661 q = 1) (hb : d277740 q = 1) : d279577 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d279577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, d279577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53662 q = 1) (hb : d277740 q = 1) : d279578 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d279578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53662, d279578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53663 q = 1) (hb : d277740 q = 1) : d279579 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d279579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d279579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53664 q = 1) (hb : d277740 q = 1) : d279580 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d279580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d279580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53665 q = 1) (hb : d277740 q = 1) : d279581 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d279581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d279581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro70316 (p : Pattern) (ha : d53671 p = 1) (hb : d277740 p = 1) : d279587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d277740 q = 1) : d277838 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d277838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69606 q ha hb
    | true =>
      simp only [d292, d277838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69607 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d277740 q = 1) : d277839 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d277839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d277839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d277740 q = 1) : d279569 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d279569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, d279569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d277740 q = 1) : d279570 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d279570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d279570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d277740 q = 1) : d279572 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d279572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, d279572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70314 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d277740 q = 1) : d279573 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d279573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, d279573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d277740 q = 1) : d279574 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d279574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, d279574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d277740 q = 1) : d279575 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d279575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, d279575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d277740 q = 1) : d279576 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d279576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, d279576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d277740 q = 1) : d279582 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d279582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, d279582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70315 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d277740 q = 1) : d279583 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d279583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, d279583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d277740 q = 1) : d279584 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d279584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, d279584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d277740 q = 1) : d279585 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d279585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, d279585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d277740 q = 1) : d279586 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d279586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, d279586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d277740 q = 1) : d279587 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d279587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, d279587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro70317 (p : Pattern) (ha : d53677 p = 1) (hb : d277740 p = 1) : d279593 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d277740 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53672 q = 1) (hb : d277740 q = 1) : d279588 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d279588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53672, d279588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70316 q ha hb
  have h3 (q : Pattern) (ha : d53673 q = 1) (hb : d277740 q = 1) : d279589 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d279589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53673, d279589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53674 q = 1) (hb : d277740 q = 1) : d279590 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d279590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53674, d279590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53675 q = 1) (hb : d277740 q = 1) : d279591 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d279591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53675, d279591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53676 q = 1) (hb : d277740 q = 1) : d279592 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d279592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53676, d279592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53677 q = 1) (hb : d277740 q = 1) : d279593 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d279593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53677, d279593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro70318 (p : Pattern) (ha : d171078 p = 1) (hb : d277740 p = 1) : d279596 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16052 q = 1) (hb : d277740 q = 1) : d278005 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d278005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69643 q ha hb
    | true =>
      simp only [d16052, d278005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69634 q ha hb
  have h2 (q : Pattern) (ha : d16053 q = 1) (hb : d277740 q = 1) : d278006 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d278006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, d278006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16054 q = 1) (hb : d277740 q = 1) : d278007 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d278007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16054, d278007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16055 q = 1) (hb : d277740 q = 1) : d278008 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d278008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d278008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16056 q = 1) (hb : d277740 q = 1) : d278009 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d278009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d278009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171078 q = 1) (hb : d277740 q = 1) : d279596 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171078, d279596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171078, d279596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70319 (p : Pattern) (ha : d171089 p = 1) (hb : d277740 p = 1) : d279607 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171084 q = 1) (hb : d277740 q = 1) : d279602 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171084, d279602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69675 q ha hb
    | true =>
      simp only [d171084, d279602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69638 q ha hb
  have h2 (q : Pattern) (ha : d171085 q = 1) (hb : d277740 q = 1) : d279603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171085, d279603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171085, d279603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171086 q = 1) (hb : d277740 q = 1) : d279604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171086, d279604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171086, d279604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171087 q = 1) (hb : d277740 q = 1) : d279605 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171087, d279605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171087, d279605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171088 q = 1) (hb : d277740 q = 1) : d279606 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171088, d279606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171088, d279606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171089 q = 1) (hb : d277740 q = 1) : d279607 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171089, d279607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171089, d279607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70320 (p : Pattern) (ha : d171095 p = 1) (hb : d277740 p = 1) : d279613 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16058 q = 1) (hb : d277740 q = 1) : d278011 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, d278011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69642 q ha hb
    | true =>
      simp only [d16058, d278011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69644 q ha hb
  have h2 (q : Pattern) (ha : d16059 q = 1) (hb : d277740 q = 1) : d278012 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, d278012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16059, d278012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171076 q = 1) (hb : d277740 q = 1) : d279594 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171076, d279594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171076, d279594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171077 q = 1) (hb : d277740 q = 1) : d279595 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171077, d279595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171077, d279595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171079 q = 1) (hb : d277740 q = 1) : d279597 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171079, d279597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171079, d279597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70318 q ha hb
  have h6 (q : Pattern) (ha : d171080 q = 1) (hb : d277740 q = 1) : d279598 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171080, d279598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171080, d279598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171081 q = 1) (hb : d277740 q = 1) : d279599 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171081, d279599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171081, d279599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171082 q = 1) (hb : d277740 q = 1) : d279600 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171082, d279600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171082, d279600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d171083 q = 1) (hb : d277740 q = 1) : d279601 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171083, d279601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171083, d279601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171090 q = 1) (hb : d277740 q = 1) : d279608 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171090, d279608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171090, d279608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70319 q ha hb
  have h11 (q : Pattern) (ha : d171091 q = 1) (hb : d277740 q = 1) : d279609 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171091, d279609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171091, d279609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171092 q = 1) (hb : d277740 q = 1) : d279610 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171092, d279610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171092, d279610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d171093 q = 1) (hb : d277740 q = 1) : d279611 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171093, d279611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171093, d279611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d171094 q = 1) (hb : d277740 q = 1) : d279612 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171094, d279612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171094, d279612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d171095 q = 1) (hb : d277740 q = 1) : d279613 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171095, d279613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171095, d279613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro70321 (p : Pattern) (ha : d171101 p = 1) (hb : d277740 p = 1) : d279619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171096 q = 1) (hb : d277740 q = 1) : d279614 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171096, d279614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171096, d279614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70320 q ha hb
  have h2 (q : Pattern) (ha : d171097 q = 1) (hb : d277740 q = 1) : d279615 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171097, d279615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171097, d279615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171098 q = 1) (hb : d277740 q = 1) : d279616 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171098, d279616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171098, d279616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171099 q = 1) (hb : d277740 q = 1) : d279617 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171099, d279617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171099, d279617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171100 q = 1) (hb : d277740 q = 1) : d279618 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171100, d279618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171100, d279618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171101 q = 1) (hb : d277740 q = 1) : d279619 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171101, d279619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171101, d279619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70322 (p : Pattern) (ha : d171105 p = 1) (hb : d277740 p = 1) : d279623 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16249 q = 1) (hb : d277740 q = 1) : d278255 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16249, d278255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69697 q ha hb
    | true =>
      simp only [d16249, d278255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69685 q ha hb
  have h2 (q : Pattern) (ha : d16250 q = 1) (hb : d277740 q = 1) : d278256 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16250, d278256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16250, d278256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16251 q = 1) (hb : d277740 q = 1) : d278257 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16251, d278257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16251, d278257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16252 q = 1) (hb : d277740 q = 1) : d278258 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16252, d278258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16252, d278258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16253 q = 1) (hb : d277740 q = 1) : d278259 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16253, d278259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16253, d278259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171105 q = 1) (hb : d277740 q = 1) : d279623 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171105, d279623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171105, d279623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70323 (p : Pattern) (ha : d171116 p = 1) (hb : d277740 p = 1) : d279634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171111 q = 1) (hb : d277740 q = 1) : d279629 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171111, d279629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69730 q ha hb
    | true =>
      simp only [d171111, d279629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69691 q ha hb
  have h2 (q : Pattern) (ha : d171112 q = 1) (hb : d277740 q = 1) : d279630 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171112, d279630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171112, d279630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171113 q = 1) (hb : d277740 q = 1) : d279631 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171113, d279631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171113, d279631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171114 q = 1) (hb : d277740 q = 1) : d279632 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171114, d279632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171114, d279632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171115 q = 1) (hb : d277740 q = 1) : d279633 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171115, d279633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171115, d279633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171116 q = 1) (hb : d277740 q = 1) : d279634 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171116, d279634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171116, d279634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70324 (p : Pattern) (ha : d171122 p = 1) (hb : d277740 p = 1) : d279640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16255 q = 1) (hb : d277740 q = 1) : d278261 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16255, d278261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69696 q ha hb
    | true =>
      simp only [d16255, d278261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69698 q ha hb
  have h2 (q : Pattern) (ha : d16256 q = 1) (hb : d277740 q = 1) : d278262 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16256, d278262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16256, d278262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171103 q = 1) (hb : d277740 q = 1) : d279621 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171103, d279621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171103, d279621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171104 q = 1) (hb : d277740 q = 1) : d279622 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171104, d279622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171104, d279622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171106 q = 1) (hb : d277740 q = 1) : d279624 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171106, d279624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171106, d279624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70322 q ha hb
  have h6 (q : Pattern) (ha : d171107 q = 1) (hb : d277740 q = 1) : d279625 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171107, d279625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171107, d279625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171108 q = 1) (hb : d277740 q = 1) : d279626 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171108, d279626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171108, d279626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171109 q = 1) (hb : d277740 q = 1) : d279627 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171109, d279627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171109, d279627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d171110 q = 1) (hb : d277740 q = 1) : d279628 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171110, d279628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171110, d279628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171117 q = 1) (hb : d277740 q = 1) : d279635 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171117, d279635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171117, d279635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70323 q ha hb
  have h11 (q : Pattern) (ha : d171118 q = 1) (hb : d277740 q = 1) : d279636 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171118, d279636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171118, d279636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171119 q = 1) (hb : d277740 q = 1) : d279637 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171119, d279637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171119, d279637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d171120 q = 1) (hb : d277740 q = 1) : d279638 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171120, d279638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171120, d279638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d171121 q = 1) (hb : d277740 q = 1) : d279639 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171121, d279639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171121, d279639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d171122 q = 1) (hb : d277740 q = 1) : d279640 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171122, d279640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171122, d279640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro70325 (p : Pattern) (ha : d171128 p = 1) (hb : d277740 p = 1) : d279646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171123 q = 1) (hb : d277740 q = 1) : d279641 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171123, d279641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171123, d279641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70324 q ha hb
  have h2 (q : Pattern) (ha : d171124 q = 1) (hb : d277740 q = 1) : d279642 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171124, d279642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171124, d279642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171125 q = 1) (hb : d277740 q = 1) : d279643 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171125, d279643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171125, d279643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171126 q = 1) (hb : d277740 q = 1) : d279644 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171126, d279644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171126, d279644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171127 q = 1) (hb : d277740 q = 1) : d279645 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171127, d279645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171127, d279645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171128 q = 1) (hb : d277740 q = 1) : d279646 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171128, d279646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171128, d279646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70326 (p : Pattern) (ha : d171133 p = 1) (hb : d277740 p = 1) : d279651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16481 q = 1) (hb : d277740 q = 1) : d278580 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16481, d278580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69751 q ha hb
    | true =>
      simp only [d16481, d278580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69752 q ha hb
  have h2 (q : Pattern) (ha : d16482 q = 1) (hb : d277740 q = 1) : d278581 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16482, d278581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16482, d278581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16483 q = 1) (hb : d277740 q = 1) : d278582 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16483, d278582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16483, d278582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16484 q = 1) (hb : d277740 q = 1) : d278583 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16484, d278583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16484, d278583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16485 q = 1) (hb : d277740 q = 1) : d278584 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16485, d278584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16485, d278584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171133 q = 1) (hb : d277740 q = 1) : d279651 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171133, d279651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171133, d279651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70327 (p : Pattern) (ha : d171140 p = 1) (hb : d277740 p = 1) : d278794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d277740 q = 1) : d278779 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d278779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69793 q ha hb
    | true =>
      simp only [d16673, d278779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69760 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d277740 q = 1) : d278780 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d278780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d278780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d277740 q = 1) : d278781 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d278781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d278781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d277740 q = 1) : d278784 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d278784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69760 q ha hb
    | true =>
      simp only [d16676, d278784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69791 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d277740 q = 1) : d278785 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d278785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d278785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d277740 q = 1) : d278786 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d278786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d278786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d277740 q = 1) : d278787 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d278787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d278787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16693 q = 1) (hb : d277740 q = 1) : d278784 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d278784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69760 q ha hb
    | true =>
      simp only [d16693, d278784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69759 q ha hb
  have h9 (q : Pattern) (ha : d16694 q = 1) (hb : d277740 q = 1) : d278785 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d278785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d278785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16695 q = 1) (hb : d277740 q = 1) : d278786 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d278786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d278786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16696 q = 1) (hb : d277740 q = 1) : d278792 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d278792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16696, d278792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171139 q = 1) (hb : d277740 q = 1) : d278793 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171139, d278793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171139, d278793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d171140 q = 1) (hb : d277740 q = 1) : d278794 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171140, d278794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171140, d278794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro70328 (p : Pattern) (ha : d171146 p = 1) (hb : d277740 p = 1) : d278808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171141 q = 1) (hb : d277740 q = 1) : d278795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171141, d278795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70327 q ha hb
    | true =>
      simp only [d171141, d278795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171142 q = 1) (hb : d277740 q = 1) : d278796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171142, d278796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171142, d278796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16699 q = 1) (hb : d277740 q = 1) : d278803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d278803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69761 q ha hb
    | true =>
      simp only [d16699, d278803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16700 q = 1) (hb : d277740 q = 1) : d278804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d278804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d278804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171143 q = 1) (hb : d277740 q = 1) : d278805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171143, d278805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171143, d278805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171144 q = 1) (hb : d277740 q = 1) : d278806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171144, d278806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171144, d278806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171145 q = 1) (hb : d277740 q = 1) : d278807 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171145, d278807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171145, d278807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171146 q = 1) (hb : d277740 q = 1) : d278808 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171146, d278808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171146, d278808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro70329 (p : Pattern) (ha : d171152 p = 1) (hb : d277740 p = 1) : d279662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171147 q = 1) (hb : d277740 q = 1) : d279657 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171147, d279657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70328 q ha hb
    | true =>
      simp only [d171147, d279657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69762 q ha hb
  have h2 (q : Pattern) (ha : d171148 q = 1) (hb : d277740 q = 1) : d279658 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171148, d279658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171148, d279658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171149 q = 1) (hb : d277740 q = 1) : d279659 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171149, d279659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171149, d279659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171150 q = 1) (hb : d277740 q = 1) : d279660 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171150, d279660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171150, d279660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171151 q = 1) (hb : d277740 q = 1) : d279661 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171151, d279661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171151, d279661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171152 q = 1) (hb : d277740 q = 1) : d279662 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171152, d279662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171152, d279662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70330 (p : Pattern) (ha : d171158 p = 1) (hb : d277740 p = 1) : d279668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16487 q = 1) (hb : d277740 q = 1) : d278586 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16487, d278586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69750 q ha hb
    | true =>
      simp only [d16487, d278586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69753 q ha hb
  have h2 (q : Pattern) (ha : d16488 q = 1) (hb : d277740 q = 1) : d278587 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16488, d278587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16488, d278587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171131 q = 1) (hb : d277740 q = 1) : d279649 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171131, d279649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171131, d279649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171132 q = 1) (hb : d277740 q = 1) : d279650 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171132, d279650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171132, d279650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171134 q = 1) (hb : d277740 q = 1) : d279652 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171134, d279652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171134, d279652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70326 q ha hb
  have h6 (q : Pattern) (ha : d171135 q = 1) (hb : d277740 q = 1) : d279653 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171135, d279653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171135, d279653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171136 q = 1) (hb : d277740 q = 1) : d279654 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171136, d279654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171136, d279654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171137 q = 1) (hb : d277740 q = 1) : d279655 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171137, d279655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171137, d279655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d171138 q = 1) (hb : d277740 q = 1) : d279656 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171138, d279656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171138, d279656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171153 q = 1) (hb : d277740 q = 1) : d279663 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171153, d279663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171153, d279663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70329 q ha hb
  have h11 (q : Pattern) (ha : d171154 q = 1) (hb : d277740 q = 1) : d279664 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171154, d279664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171154, d279664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171155 q = 1) (hb : d277740 q = 1) : d279665 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171155, d279665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171155, d279665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d171156 q = 1) (hb : d277740 q = 1) : d279666 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171156, d279666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171156, d279666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d171157 q = 1) (hb : d277740 q = 1) : d279667 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171157, d279667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171157, d279667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d171158 q = 1) (hb : d277740 q = 1) : d279668 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171158, d279668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171158, d279668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro70331 (p : Pattern) (ha : d171164 p = 1) (hb : d277740 p = 1) : d279674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171159 q = 1) (hb : d277740 q = 1) : d279669 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171159, d279669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171159, d279669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70330 q ha hb
  have h2 (q : Pattern) (ha : d171160 q = 1) (hb : d277740 q = 1) : d279670 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171160, d279670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171160, d279670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171161 q = 1) (hb : d277740 q = 1) : d279671 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171161, d279671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171161, d279671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171162 q = 1) (hb : d277740 q = 1) : d279672 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171162, d279672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171162, d279672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171163 q = 1) (hb : d277740 q = 1) : d279673 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171163, d279673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171163, d279673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171164 q = 1) (hb : d277740 q = 1) : d279674 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171164, d279674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171164, d279674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70332 (p : Pattern) (ha : d212441 p = 1) (hb : d277740 p = 1) : d279680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27604 q = 1) (hb : d277740 q = 1) : d278944 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27604, d278944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69830 q ha hb
    | true =>
      simp only [d27604, d278944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69831 q ha hb
  have h2 (q : Pattern) (ha : d27605 q = 1) (hb : d277740 q = 1) : d278945 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27605, d278945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27605, d278945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27606 q = 1) (hb : d277740 q = 1) : d278946 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27606, d278946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27606, d278946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27607 q = 1) (hb : d277740 q = 1) : d278947 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27607, d278947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27607, d278947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27608 q = 1) (hb : d277740 q = 1) : d278948 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27608, d278948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27608, d278948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212441 q = 1) (hb : d277740 q = 1) : d279680 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212441, d279680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212441, d279680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70333 (p : Pattern) (ha : d212448 p = 1) (hb : d277740 p = 1) : d279137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27923 q = 1) (hb : d277740 q = 1) : d279122 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27923, d279122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69869 q ha hb
    | true =>
      simp only [d27923, d279122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69838 q ha hb
  have h2 (q : Pattern) (ha : d27924 q = 1) (hb : d277740 q = 1) : d279123 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27924, d279123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27924, d279123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27925 q = 1) (hb : d277740 q = 1) : d279124 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27925, d279124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27925, d279124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27937 q = 1) (hb : d277740 q = 1) : d279127 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27937, d279127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69838 q ha hb
    | true =>
      simp only [d27937, d279127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69871 q ha hb
  have h5 (q : Pattern) (ha : d27938 q = 1) (hb : d277740 q = 1) : d279128 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27938, d279128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27938, d279128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27939 q = 1) (hb : d277740 q = 1) : d279129 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27939, d279129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27939, d279129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27940 q = 1) (hb : d277740 q = 1) : d279130 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27940, d279130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27940, d279130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27960 q = 1) (hb : d277740 q = 1) : d279127 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27960, d279127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69838 q ha hb
    | true =>
      simp only [d27960, d279127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69839 q ha hb
  have h9 (q : Pattern) (ha : d27961 q = 1) (hb : d277740 q = 1) : d279128 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27961, d279128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27961, d279128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27962 q = 1) (hb : d277740 q = 1) : d279129 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27962, d279129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27962, d279129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27963 q = 1) (hb : d277740 q = 1) : d279135 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27963, d279135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27963, d279135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d212447 q = 1) (hb : d277740 q = 1) : d279136 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d212447, d279136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212447, d279136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d212448 q = 1) (hb : d277740 q = 1) : d279137 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d212448, d279137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d212448, d279137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro70334 (p : Pattern) (ha : d212454 p = 1) (hb : d277740 p = 1) : d279151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212449 q = 1) (hb : d277740 q = 1) : d279138 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d212449, d279138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70333 q ha hb
    | true =>
      simp only [d212449, d279138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212450 q = 1) (hb : d277740 q = 1) : d279139 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d212450, d279139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212450, d279139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27966 q = 1) (hb : d277740 q = 1) : d279146 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27966, d279146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69840 q ha hb
    | true =>
      simp only [d27966, d279146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27967 q = 1) (hb : d277740 q = 1) : d279147 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27967, d279147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27967, d279147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212451 q = 1) (hb : d277740 q = 1) : d279148 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d212451, d279148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212451, d279148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212452 q = 1) (hb : d277740 q = 1) : d279149 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d212452, d279149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212452, d279149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d212453 q = 1) (hb : d277740 q = 1) : d279150 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d212453, d279150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212453, d279150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d212454 q = 1) (hb : d277740 q = 1) : d279151 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d212454, d279151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212454, d279151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro70335 (p : Pattern) (ha : d212460 p = 1) (hb : d277740 p = 1) : d279691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212455 q = 1) (hb : d277740 q = 1) : d279686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d212455, d279686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70334 q ha hb
    | true =>
      simp only [d212455, d279686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69841 q ha hb
  have h2 (q : Pattern) (ha : d212456 q = 1) (hb : d277740 q = 1) : d279687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212456, d279687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212456, d279687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d212457 q = 1) (hb : d277740 q = 1) : d279688 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212457, d279688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212457, d279688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212458 q = 1) (hb : d277740 q = 1) : d279689 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212458, d279689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212458, d279689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212459 q = 1) (hb : d277740 q = 1) : d279690 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212459, d279690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212459, d279690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212460 q = 1) (hb : d277740 q = 1) : d279691 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212460, d279691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212460, d279691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70336 (p : Pattern) (ha : d212466 p = 1) (hb : d277740 p = 1) : d279697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27610 q = 1) (hb : d277740 q = 1) : d278950 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27610, d278950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69829 q ha hb
    | true =>
      simp only [d27610, d278950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69832 q ha hb
  have h2 (q : Pattern) (ha : d27611 q = 1) (hb : d277740 q = 1) : d278951 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d27611, d278951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27611, d278951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212439 q = 1) (hb : d277740 q = 1) : d279678 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212439, d279678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212439, d279678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212440 q = 1) (hb : d277740 q = 1) : d279679 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212440, d279679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212440, d279679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212442 q = 1) (hb : d277740 q = 1) : d279681 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212442, d279681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212442, d279681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70332 q ha hb
  have h6 (q : Pattern) (ha : d212443 q = 1) (hb : d277740 q = 1) : d279682 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212443, d279682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212443, d279682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d212444 q = 1) (hb : d277740 q = 1) : d279683 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212444, d279683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212444, d279683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d212445 q = 1) (hb : d277740 q = 1) : d279684 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212445, d279684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212445, d279684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d212446 q = 1) (hb : d277740 q = 1) : d279685 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212446, d279685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212446, d279685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d212461 q = 1) (hb : d277740 q = 1) : d279692 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212461, d279692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212461, d279692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70335 q ha hb
  have h11 (q : Pattern) (ha : d212462 q = 1) (hb : d277740 q = 1) : d279693 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212462, d279693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212462, d279693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d212463 q = 1) (hb : d277740 q = 1) : d279694 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212463, d279694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d212463, d279694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d212464 q = 1) (hb : d277740 q = 1) : d279695 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212464, d279695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d212464, d279695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d212465 q = 1) (hb : d277740 q = 1) : d279696 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212465, d279696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d212465, d279696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d212466 q = 1) (hb : d277740 q = 1) : d279697 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d212466, d279697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d212466, d279697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro70337 (p : Pattern) (ha : d212472 p = 1) (hb : d277740 p = 1) : d279703 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212467 q = 1) (hb : d277740 q = 1) : d279698 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d212467, d279698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212467, d279698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70336 q ha hb
  have h2 (q : Pattern) (ha : d212468 q = 1) (hb : d277740 q = 1) : d279699 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d212468, d279699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212468, d279699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d212469 q = 1) (hb : d277740 q = 1) : d279700 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d212469, d279700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212469, d279700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d212470 q = 1) (hb : d277740 q = 1) : d279701 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d212470, d279701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212470, d279701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212471 q = 1) (hb : d277740 q = 1) : d279702 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d212471, d279702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212471, d279702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212472 q = 1) (hb : d277740 q = 1) : d279703 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d212472, d279703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212472, d279703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70338 (p : Pattern) (ha : d212479 p = 1) (hb : d277740 p = 1) : d279710 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28218 q = 1) (hb : d277740 q = 1) : d279281 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28218, d279281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69906 q ha hb
    | true =>
      simp only [d28218, d279281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69907 q ha hb
  have h2 (q : Pattern) (ha : d28219 q = 1) (hb : d277740 q = 1) : d279282 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28219, d279282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28219, d279282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28220 q = 1) (hb : d277740 q = 1) : d279283 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28220, d279283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28220, d279283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28221 q = 1) (hb : d277740 q = 1) : d279284 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28221, d279284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28221, d279284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28222 q = 1) (hb : d277740 q = 1) : d279285 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28222, d279285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28222, d279285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212479 q = 1) (hb : d277740 q = 1) : d279710 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212479, d279710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212479, d279710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70339 (p : Pattern) (ha : d212486 p = 1) (hb : d277740 p = 1) : d279717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28523 q = 1) (hb : d277740 q = 1) : d279437 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28523, d279437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69943 q ha hb
    | true =>
      simp only [d28523, d279437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69914 q ha hb
  have h2 (q : Pattern) (ha : d28524 q = 1) (hb : d277740 q = 1) : d279438 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28524, d279438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28524, d279438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28525 q = 1) (hb : d277740 q = 1) : d279439 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28525, d279439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28525, d279439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28537 q = 1) (hb : d277740 q = 1) : d279446 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28537, d279446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69914 q ha hb
    | true =>
      simp only [d28537, d279446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69945 q ha hb
  have h5 (q : Pattern) (ha : d28538 q = 1) (hb : d277740 q = 1) : d279447 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28538, d279447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28538, d279447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28539 q = 1) (hb : d277740 q = 1) : d279448 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28539, d279448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28539, d279448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28540 q = 1) (hb : d277740 q = 1) : d279449 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28540, d279449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28540, d279449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28560 q = 1) (hb : d277740 q = 1) : d279465 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28560, d279465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69914 q ha hb
    | true =>
      simp only [d28560, d279465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69915 q ha hb
  have h9 (q : Pattern) (ha : d28561 q = 1) (hb : d277740 q = 1) : d279466 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28561, d279466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28561, d279466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28562 q = 1) (hb : d277740 q = 1) : d279467 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28562, d279467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28562, d279467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28563 q = 1) (hb : d277740 q = 1) : d279468 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28563, d279468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28563, d279468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d212485 q = 1) (hb : d277740 q = 1) : d279716 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d212485, d279716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212485, d279716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d212486 q = 1) (hb : d277740 q = 1) : d279717 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d212486, d279717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d212486, d279717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro70340 (p : Pattern) (ha : d212492 p = 1) (hb : d277740 p = 1) : d279723 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212487 q = 1) (hb : d277740 q = 1) : d279718 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d212487, d279718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70339 q ha hb
    | true =>
      simp only [d212487, d279718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212488 q = 1) (hb : d277740 q = 1) : d279719 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d212488, d279719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212488, d279719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28566 q = 1) (hb : d277740 q = 1) : d279471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28566, d279471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69916 q ha hb
    | true =>
      simp only [d28566, d279471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28567 q = 1) (hb : d277740 q = 1) : d279472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28567, d279472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28567, d279472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212489 q = 1) (hb : d277740 q = 1) : d279720 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d212489, d279720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212489, d279720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212490 q = 1) (hb : d277740 q = 1) : d279721 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d212490, d279721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212490, d279721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d212491 q = 1) (hb : d277740 q = 1) : d279722 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d212491, d279722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212491, d279722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d212492 q = 1) (hb : d277740 q = 1) : d279723 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d212492, d279723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212492, d279723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro70341 (p : Pattern) (ha : d212498 p = 1) (hb : d277740 p = 1) : d279729 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212493 q = 1) (hb : d277740 q = 1) : d279724 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d212493, d279724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70340 q ha hb
    | true =>
      simp only [d212493, d279724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69917 q ha hb
  have h2 (q : Pattern) (ha : d212494 q = 1) (hb : d277740 q = 1) : d279725 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212494, d279725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212494, d279725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d212495 q = 1) (hb : d277740 q = 1) : d279726 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212495, d279726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212495, d279726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212496 q = 1) (hb : d277740 q = 1) : d279727 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212496, d279727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212496, d279727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212497 q = 1) (hb : d277740 q = 1) : d279728 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212497, d279728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212497, d279728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212498 q = 1) (hb : d277740 q = 1) : d279729 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212498, d279729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212498, d279729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70342 (p : Pattern) (ha : d212504 p = 1) (hb : d277740 p = 1) : d279735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28224 q = 1) (hb : d277740 q = 1) : d279287 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28224, d279287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69905 q ha hb
    | true =>
      simp only [d28224, d279287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69908 q ha hb
  have h2 (q : Pattern) (ha : d28225 q = 1) (hb : d277740 q = 1) : d279288 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d28225, d279288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28225, d279288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212477 q = 1) (hb : d277740 q = 1) : d279708 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212477, d279708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212477, d279708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212478 q = 1) (hb : d277740 q = 1) : d279709 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212478, d279709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212478, d279709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212480 q = 1) (hb : d277740 q = 1) : d279711 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212480, d279711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212480, d279711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70338 q ha hb
  have h6 (q : Pattern) (ha : d212481 q = 1) (hb : d277740 q = 1) : d279712 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212481, d279712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212481, d279712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d212482 q = 1) (hb : d277740 q = 1) : d279713 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212482, d279713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212482, d279713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d212483 q = 1) (hb : d277740 q = 1) : d279714 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212483, d279714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212483, d279714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d212484 q = 1) (hb : d277740 q = 1) : d279715 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212484, d279715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212484, d279715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d212499 q = 1) (hb : d277740 q = 1) : d279730 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212499, d279730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212499, d279730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70341 q ha hb
  have h11 (q : Pattern) (ha : d212500 q = 1) (hb : d277740 q = 1) : d279731 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212500, d279731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212500, d279731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d212501 q = 1) (hb : d277740 q = 1) : d279732 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212501, d279732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d212501, d279732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d212502 q = 1) (hb : d277740 q = 1) : d279733 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212502, d279733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d212502, d279733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d212503 q = 1) (hb : d277740 q = 1) : d279734 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212503, d279734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d212503, d279734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d212504 q = 1) (hb : d277740 q = 1) : d279735 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d212504, d279735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d212504, d279735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro70343 (p : Pattern) (ha : d212510 p = 1) (hb : d277740 p = 1) : d279741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212505 q = 1) (hb : d277740 q = 1) : d279736 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d212505, d279736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212505, d279736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70342 q ha hb
  have h2 (q : Pattern) (ha : d212506 q = 1) (hb : d277740 q = 1) : d279737 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d212506, d279737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212506, d279737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d212507 q = 1) (hb : d277740 q = 1) : d279738 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d212507, d279738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212507, d279738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d212508 q = 1) (hb : d277740 q = 1) : d279739 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d212508, d279739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212508, d279739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212509 q = 1) (hb : d277740 q = 1) : d279740 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d212509, d279740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212509, d279740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212510 q = 1) (hb : d277740 q = 1) : d279741 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d212510, d279741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212510, d279741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70344 (p : Pattern) (ha : d212516 p = 1) (hb : d277740 p = 1) : d279747 p = 1 := by
  have h0 (q : Pattern) (ha : d171102 q = 1) (hb : d277740 q = 1) : d279620 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171102, d279620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70317 q ha hb
    | true =>
      simp only [d171102, d279620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70321 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d171129 q = 1) (hb : d277740 q = 1) : d279647 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171129, d279647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171129, d279647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70325 q ha hb
  have h3 (q : Pattern) (ha : d171130 q = 1) (hb : d277740 q = 1) : d279648 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171130, d279648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171130, d279648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171165 q = 1) (hb : d277740 q = 1) : d279675 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171165, d279675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171165, d279675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70331 q ha hb
  have h5 (q : Pattern) (ha : d171166 q = 1) (hb : d277740 q = 1) : d279676 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171166, d279676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171166, d279676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171167 q = 1) (hb : d277740 q = 1) : d279677 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171167, d279677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171167, d279677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d212473 q = 1) (hb : d277740 q = 1) : d279704 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d212473, d279704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212473, d279704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70337 q ha hb
  have h8 (q : Pattern) (ha : d212474 q = 1) (hb : d277740 q = 1) : d279705 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d212474, d279705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212474, d279705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d212475 q = 1) (hb : d277740 q = 1) : d279706 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d212475, d279706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212475, d279706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d212476 q = 1) (hb : d277740 q = 1) : d279707 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d212476, d279707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212476, d279707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d212511 q = 1) (hb : d277740 q = 1) : d279742 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d212511, d279742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212511, d279742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70343 q ha hb
  have h12 (q : Pattern) (ha : d212512 q = 1) (hb : d277740 q = 1) : d279743 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d212512, d279743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212512, d279743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d212513 q = 1) (hb : d277740 q = 1) : d279744 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d212513, d279744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212513, d279744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d212514 q = 1) (hb : d277740 q = 1) : d279745 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d212514, d279745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212514, d279745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d212515 q = 1) (hb : d277740 q = 1) : d279746 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d212515, d279746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212515, d279746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d212516 q = 1) (hb : d277740 q = 1) : d279747 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d212516, d279747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d212516, d279747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro70345 (p : Pattern) (ha : d212522 p = 1) (hb : d277740 p = 1) : d279753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212517 q = 1) (hb : d277740 q = 1) : d279748 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d212517, d279748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70344 q ha hb
    | true =>
      simp only [d212517, d279748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212518 q = 1) (hb : d277740 q = 1) : d279749 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d212518, d279749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212518, d279749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212519 q = 1) (hb : d277740 q = 1) : d279750 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d212519, d279750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212519, d279750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212520 q = 1) (hb : d277740 q = 1) : d279751 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d212520, d279751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212520, d279751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212521 q = 1) (hb : d277740 q = 1) : d279752 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d212521, d279752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212521, d279752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212522 q = 1) (hb : d277740 q = 1) : d279753 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d212522, d279753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212522, d279753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro70346 (p : Pattern) (ha : d212528 p = 1) (hb : d277740 p = 1) : d279759 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212523 q = 1) (hb : d277740 q = 1) : d279754 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d212523, d279754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70345 q ha hb
    | true =>
      simp only [d212523, d279754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212524 q = 1) (hb : d277740 q = 1) : d279755 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d212524, d279755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212524, d279755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212525 q = 1) (hb : d277740 q = 1) : d279756 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d212525, d279756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212525, d279756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212526 q = 1) (hb : d277740 q = 1) : d279757 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d212526, d279757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212526, d279757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212527 q = 1) (hb : d277740 q = 1) : d279758 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d212527, d279758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212527, d279758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212528 q = 1) (hb : d277740 q = 1) : d279759 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d212528, d279759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212528, d279759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro70347 (p : Pattern) (ha : d212534 p = 1) (hb : d277740 p = 1) : d279765 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212529 q = 1) (hb : d277740 q = 1) : d279760 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d212529, d279760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70346 q ha hb
    | true =>
      simp only [d212529, d279760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212530 q = 1) (hb : d277740 q = 1) : d279761 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d212530, d279761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212530, d279761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212531 q = 1) (hb : d277740 q = 1) : d279762 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d212531, d279762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212531, d279762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212532 q = 1) (hb : d277740 q = 1) : d279763 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d212532, d279763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212532, d279763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212533 q = 1) (hb : d277740 q = 1) : d279764 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d212533, d279764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212533, d279764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212534 q = 1) (hb : d277740 q = 1) : d279765 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d212534, d279765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212534, d279765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro70348 (p : Pattern) (ha : d212540 p = 1) (hb : d277740 p = 1) : d279771 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212535 q = 1) (hb : d277740 q = 1) : d279766 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d212535, d279766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70347 q ha hb
    | true =>
      simp only [d212535, d279766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212536 q = 1) (hb : d277740 q = 1) : d279767 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d212536, d279767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212536, d279767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212537 q = 1) (hb : d277740 q = 1) : d279768 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d212537, d279768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212537, d279768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212538 q = 1) (hb : d277740 q = 1) : d279769 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d212538, d279769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212538, d279769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212539 q = 1) (hb : d277740 q = 1) : d279770 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d212539, d279770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212539, d279770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212540 q = 1) (hb : d277740 q = 1) : d279771 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d212540, d279771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212540, d279771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro70349 (p : Pattern) (ha : d212546 p = 1) (hb : d277740 p = 1) : d279777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212541 q = 1) (hb : d277740 q = 1) : d279772 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d212541, d279772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70348 q ha hb
    | true =>
      simp only [d212541, d279772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212542 q = 1) (hb : d277740 q = 1) : d279773 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d212542, d279773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212542, d279773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212543 q = 1) (hb : d277740 q = 1) : d279774 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d212543, d279774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212543, d279774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212544 q = 1) (hb : d277740 q = 1) : d279775 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d212544, d279775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212544, d279775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212545 q = 1) (hb : d277740 q = 1) : d279776 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d212545, d279776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212545, d279776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212546 q = 1) (hb : d277740 q = 1) : d279777 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d212546, d279777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212546, d279777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro70350 (p : Pattern) (ha : d212552 p = 1) (hb : d277740 p = 1) : d279783 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212547 q = 1) (hb : d277740 q = 1) : d279778 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d212547, d279778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70349 q ha hb
    | true =>
      simp only [d212547, d279778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212548 q = 1) (hb : d277740 q = 1) : d279779 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d212548, d279779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212548, d279779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212549 q = 1) (hb : d277740 q = 1) : d279780 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d212549, d279780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212549, d279780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212550 q = 1) (hb : d277740 q = 1) : d279781 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d212550, d279781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212550, d279781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212551 q = 1) (hb : d277740 q = 1) : d279782 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d212551, d279782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212551, d279782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212552 q = 1) (hb : d277740 q = 1) : d279783 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d212552, d279783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212552, d279783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro70351 (p : Pattern) (ha : d212558 p = 1) (hb : d277740 p = 1) : d279789 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212553 q = 1) (hb : d277740 q = 1) : d279784 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d212553, d279784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70350 q ha hb
    | true =>
      simp only [d212553, d279784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212554 q = 1) (hb : d277740 q = 1) : d279785 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d212554, d279785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212554, d279785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212555 q = 1) (hb : d277740 q = 1) : d279786 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d212555, d279786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212555, d279786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212556 q = 1) (hb : d277740 q = 1) : d279787 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d212556, d279787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212556, d279787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212557 q = 1) (hb : d277740 q = 1) : d279788 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d212557, d279788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212557, d279788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212558 q = 1) (hb : d277740 q = 1) : d279789 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d212558, d279789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212558, d279789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro70352 (p : Pattern) (ha : d262145 p = 1) (hb : d277830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262093 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262099 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d262134 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d262013 q = 1) (hb : d277766 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262013, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69968 q ha hb
    | true =>
      simp only [d262013, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d262135 q = 1) (hb : d277826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262135, d277826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d262135, d277826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d262141 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d262142 q = 1) (hb : d277827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262142, d277827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d262142, d277827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d262143 q = 1) (hb : d277828 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262143, d277828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262143, d277828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d262144 q = 1) (hb : d277829 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262144, d277829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262144, d277829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d262145 q = 1) (hb : d277830 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262145, d277830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262145, d277830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro70353 (p : Pattern) (ha : d262164 p = 1) (hb : d277837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262134 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262013 q = 1) (hb : d277766 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262013, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69968 q ha hb
    | true =>
      simp only [d262013, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d262135 q = 1) (hb : d277826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262135, d277826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262135, d277826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d262141 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d262142 q = 1) (hb : d277827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262142, d277827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d262142, d277827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d262143 q = 1) (hb : d277828 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262143, d277828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262143, d277828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262144 q = 1) (hb : d277829 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262144, d277829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262144, d277829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d262150 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d262154 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d262156 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d262020 q = 1) (hb : d277773 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262020, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69970 q ha hb
    | true =>
      simp only [d262020, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d262157 q = 1) (hb : d277833 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262157, d277833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d262157, d277833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262160 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262161 q = 1) (hb : d277834 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262161, d277834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262161, d277834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262162 q = 1) (hb : d277835 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262162, d277835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d262162, d277835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d262163 q = 1) (hb : d277836 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262163, d277836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d262163, d277836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d262164 q = 1) (hb : d277837 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262164, d277837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d262164, d277837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro70354 (p : Pattern) (ha : d262173 p = 1) (hb : d279571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262156 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262020 q = 1) (hb : d277773 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262020, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69970 q ha hb
    | true =>
      simp only [d262020, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d262157 q = 1) (hb : d277833 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262157, d277833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262157, d277833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262160 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262161 q = 1) (hb : d277834 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262161, d277834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262161, d277834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262171 q = 1) (hb : d277835 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262171, d277835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262171, d277835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262172 q = 1) (hb : d277836 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262172, d277836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262172, d277836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262173 q = 1) (hb : d279571 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262173, d279571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262173, d279571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70355 (p : Pattern) (ha : d262213 p = 1) (hb : d279581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262202 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262056 q = 1) (hb : d277809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262056, d277809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69975 q ha hb
    | true =>
      simp only [d262056, d277809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d262203 q = 1) (hb : d279577 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262203, d279577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262203, d279577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262209 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262210 q = 1) (hb : d279578 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262210, d279578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262210, d279578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262211 q = 1) (hb : d279579 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262211, d279579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262211, d279579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262212 q = 1) (hb : d279580 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262212, d279580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262212, d279580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262213 q = 1) (hb : d279581 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262213, d279581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262213, d279581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70356 (p : Pattern) (ha : d262219 p = 1) (hb : d279587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262087 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262165 q = 1) (hb : d277838 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262165, d277838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70352 q ha hb
    | true =>
      simp only [d262165, d277838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70353 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262167 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262168 q = 1) (hb : d277839 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262168, d277839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d262168, d277839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262169 q = 1) (hb : d279569 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262169, d279569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262169, d279569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262170 q = 1) (hb : d279570 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262170, d279570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262170, d279570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262174 q = 1) (hb : d279572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262174, d279572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262174, d279572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70354 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d262175 q = 1) (hb : d279573 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262175, d279573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d262175, d279573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d262176 q = 1) (hb : d279574 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262176, d279574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d262176, d279574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d262177 q = 1) (hb : d279575 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262177, d279575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d262177, d279575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d262178 q = 1) (hb : d279576 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262178, d279576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d262178, d279576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d262214 q = 1) (hb : d279582 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262214, d279582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262214, d279582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70355 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262215 q = 1) (hb : d279583 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262215, d279583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262215, d279583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262216 q = 1) (hb : d279584 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262216, d279584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d262216, d279584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d262217 q = 1) (hb : d279585 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262217, d279585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d262217, d279585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d262218 q = 1) (hb : d279586 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262218, d279586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d262218, d279586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d262219 q = 1) (hb : d279587 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d262219, d279587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d262219, d279587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro70357 (p : Pattern) (ha : d262225 p = 1) (hb : d279593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d262068 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d262068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d262068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66694 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d262069 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d262069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d262069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d262070 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d262070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d262070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d262071 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d262071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d262071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d262072 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d262072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d262072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262220 q = 1) (hb : d279588 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d262220, d279588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262220, d279588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70356 q ha hb
  have h8 (q : Pattern) (ha : d262221 q = 1) (hb : d279589 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d262221, d279589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262221, d279589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d262222 q = 1) (hb : d279590 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d262222, d279590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262222, d279590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d262223 q = 1) (hb : d279591 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d262223, d279591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262223, d279591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d262224 q = 1) (hb : d279592 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d262224, d279592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262224, d279592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d262225 q = 1) (hb : d279593 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d262225, d279593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d262225, d279593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro70358 (p : Pattern) (ha : d262339 p = 1) (hb : d278000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262269 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262278 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d262328 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d262243 q = 1) (hb : d277995 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262243, d277995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70006 q ha hb
    | true =>
      simp only [d262243, d277995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70007 q ha hb
  have h5 (q : Pattern) (ha : d262329 q = 1) (hb : d277996 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262329, d277996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d262329, d277996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d262335 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d262336 q = 1) (hb : d277997 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262336, d277997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d262336, d277997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d262337 q = 1) (hb : d277998 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262337, d277998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262337, d277998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d262338 q = 1) (hb : d277999 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262338, d277999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262338, d277999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d262339 q = 1) (hb : d278000 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262339, d278000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262339, d278000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro70359 (p : Pattern) (ha : d262360 p = 1) (hb : d278010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262278 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262328 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262243 q = 1) (hb : d277995 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262243, d277995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70006 q ha hb
    | true =>
      simp only [d262243, d277995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70007 q ha hb
  have h4 (q : Pattern) (ha : d262329 q = 1) (hb : d277996 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262329, d277996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262329, d277996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d262335 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d262336 q = 1) (hb : d277997 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262336, d277997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d262336, d277997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d262337 q = 1) (hb : d277998 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262337, d277998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262337, d277998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262338 q = 1) (hb : d277999 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262338, d277999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262338, d277999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d262345 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d262350 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d262352 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d262253 q = 1) (hb : d278005 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262253, d278005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70009 q ha hb
    | true =>
      simp only [d262253, d278005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70010 q ha hb
  have h13 (q : Pattern) (ha : d262353 q = 1) (hb : d278006 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262353, d278006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d262353, d278006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262356 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262357 q = 1) (hb : d278007 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262357, d278007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262357, d278007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262358 q = 1) (hb : d278008 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262358, d278008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d262358, d278008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d262359 q = 1) (hb : d278009 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262359, d278009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d262359, d278009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d262360 q = 1) (hb : d278010 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262360, d278010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d262360, d278010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro70360 (p : Pattern) (ha : d262380 p = 1) (hb : d279596 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262352 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262253 q = 1) (hb : d278005 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262253, d278005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70009 q ha hb
    | true =>
      simp only [d262253, d278005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70010 q ha hb
  have h3 (q : Pattern) (ha : d262353 q = 1) (hb : d278006 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262353, d278006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262353, d278006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262356 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262357 q = 1) (hb : d278007 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262357, d278007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262357, d278007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262378 q = 1) (hb : d278008 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262378, d278008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262378, d278008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262379 q = 1) (hb : d278009 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262379, d278009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262379, d278009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262380 q = 1) (hb : d279596 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262380, d279596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262380, d279596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70361 (p : Pattern) (ha : d262448 p = 1) (hb : d279607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262432 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262437 q = 1) (hb : d279602 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262437, d279602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70044 q ha hb
    | true =>
      simp only [d262437, d279602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70047 q ha hb
  have h3 (q : Pattern) (ha : d262438 q = 1) (hb : d279603 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262438, d279603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262438, d279603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262444 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262445 q = 1) (hb : d279604 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262445, d279604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262445, d279604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262446 q = 1) (hb : d279605 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262446, d279605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262446, d279605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262447 q = 1) (hb : d279606 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262447, d279606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262447, d279606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262448 q = 1) (hb : d279607 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262448, d279607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262448, d279607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70362 (p : Pattern) (ha : d262461 p = 1) (hb : d279613 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262261 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262361 q = 1) (hb : d278011 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262361, d278011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70358 q ha hb
    | true =>
      simp only [d262361, d278011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70359 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262374 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262375 q = 1) (hb : d278012 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262375, d278012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d262375, d278012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262376 q = 1) (hb : d279594 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262376, d279594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262376, d279594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262377 q = 1) (hb : d279595 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262377, d279595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262377, d279595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262381 q = 1) (hb : d279597 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262381, d279597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262381, d279597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70360 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d262383 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d262384 q = 1) (hb : d279598 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262384, d279598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d262384, d279598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d262385 q = 1) (hb : d279599 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262385, d279599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d262385, d279599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d262386 q = 1) (hb : d279600 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262386, d279600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d262386, d279600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d262387 q = 1) (hb : d279601 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262387, d279601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d262387, d279601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d262449 q = 1) (hb : d279608 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262449, d279608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262449, d279608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70361 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262456 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262457 q = 1) (hb : d279609 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262457, d279609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262457, d279609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262458 q = 1) (hb : d279610 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262458, d279610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d262458, d279610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d262459 q = 1) (hb : d279611 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262459, d279611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d262459, d279611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d262460 q = 1) (hb : d279612 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262460, d279612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d262460, d279612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d262461 q = 1) (hb : d279613 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d262461, d279613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d262461, d279613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro70363 (p : Pattern) (ha : d262467 p = 1) (hb : d279619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262462 q = 1) (hb : d279614 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d262462, d279614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262462, d279614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70362 q ha hb
  have h2 (q : Pattern) (ha : d262463 q = 1) (hb : d279615 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d262463, d279615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262463, d279615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d262464 q = 1) (hb : d279616 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d262464, d279616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262464, d279616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d262465 q = 1) (hb : d279617 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d262465, d279617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262465, d279617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d262466 q = 1) (hb : d279618 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d262466, d279618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262466, d279618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d262467 q = 1) (hb : d279619 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d262467, d279619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262467, d279619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70364 (p : Pattern) (ha : d262607 p = 1) (hb : d278250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262530 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262539 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d262596 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d262504 q = 1) (hb : d278245 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262504, d278245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70057 q ha hb
    | true =>
      simp only [d262504, d278245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70058 q ha hb
  have h5 (q : Pattern) (ha : d262597 q = 1) (hb : d278246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262597, d278246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d262597, d278246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d262603 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d262604 q = 1) (hb : d278247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262604, d278247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d262604, d278247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d262605 q = 1) (hb : d278248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262605, d278248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262605, d278248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d262606 q = 1) (hb : d278249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262606, d278249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262606, d278249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d262607 q = 1) (hb : d278250 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262607, d278250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262607, d278250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro70365 (p : Pattern) (ha : d262628 p = 1) (hb : d278260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262530 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262539 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262596 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262504 q = 1) (hb : d278245 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262504, d278245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70057 q ha hb
    | true =>
      simp only [d262504, d278245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70058 q ha hb
  have h4 (q : Pattern) (ha : d262597 q = 1) (hb : d278246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262597, d278246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262597, d278246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d262603 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d262604 q = 1) (hb : d278247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262604, d278247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d262604, d278247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d262605 q = 1) (hb : d278248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262605, d278248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262605, d278248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262606 q = 1) (hb : d278249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262606, d278249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262606, d278249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d262613 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d262618 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d262620 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d262514 q = 1) (hb : d278255 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262514, d278255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70060 q ha hb
    | true =>
      simp only [d262514, d278255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70061 q ha hb
  have h13 (q : Pattern) (ha : d262621 q = 1) (hb : d278256 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262621, d278256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d262621, d278256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262624 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262625 q = 1) (hb : d278257 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262625, d278257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262625, d278257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262626 q = 1) (hb : d278258 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262626, d278258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d262626, d278258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d262627 q = 1) (hb : d278259 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262627, d278259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d262627, d278259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d262628 q = 1) (hb : d278260 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262628, d278260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d262628, d278260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro70366 (p : Pattern) (ha : d262648 p = 1) (hb : d279623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262620 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262514 q = 1) (hb : d278255 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262514, d278255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70060 q ha hb
    | true =>
      simp only [d262514, d278255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70061 q ha hb
  have h3 (q : Pattern) (ha : d262621 q = 1) (hb : d278256 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262621, d278256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262621, d278256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262624 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262625 q = 1) (hb : d278257 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262625, d278257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262625, d278257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262646 q = 1) (hb : d278258 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262646, d278258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262646, d278258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262647 q = 1) (hb : d278259 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262647, d278259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262647, d278259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262648 q = 1) (hb : d279623 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262648, d279623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262648, d279623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70367 (p : Pattern) (ha : d262733 p = 1) (hb : d279634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262717 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262722 q = 1) (hb : d279629 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262722, d279629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70099 q ha hb
    | true =>
      simp only [d262722, d279629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70102 q ha hb
  have h3 (q : Pattern) (ha : d262723 q = 1) (hb : d279630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262723, d279630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262723, d279630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262729 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262730 q = 1) (hb : d279631 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262730, d279631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262730, d279631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262731 q = 1) (hb : d279632 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262731, d279632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262731, d279632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262732 q = 1) (hb : d279633 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262732, d279633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262732, d279633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262733 q = 1) (hb : d279634 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262733, d279634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262733, d279634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70368 (p : Pattern) (ha : d262746 p = 1) (hb : d279640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262522 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262629 q = 1) (hb : d278261 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262629, d278261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70364 q ha hb
    | true =>
      simp only [d262629, d278261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70365 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262642 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262643 q = 1) (hb : d278262 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262643, d278262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d262643, d278262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262644 q = 1) (hb : d279621 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262644, d279621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262644, d279621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262645 q = 1) (hb : d279622 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262645, d279622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262645, d279622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262649 q = 1) (hb : d279624 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262649, d279624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262649, d279624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70366 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d262651 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d262652 q = 1) (hb : d279625 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262652, d279625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d262652, d279625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d262653 q = 1) (hb : d279626 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262653, d279626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d262653, d279626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d262654 q = 1) (hb : d279627 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262654, d279627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d262654, d279627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d262655 q = 1) (hb : d279628 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262655, d279628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d262655, d279628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d262734 q = 1) (hb : d279635 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262734, d279635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262734, d279635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70367 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262741 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262742 q = 1) (hb : d279636 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262742, d279636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262742, d279636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262743 q = 1) (hb : d279637 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262743, d279637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d262743, d279637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d262744 q = 1) (hb : d279638 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262744, d279638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d262744, d279638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d262745 q = 1) (hb : d279639 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262745, d279639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d262745, d279639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d262746 q = 1) (hb : d279640 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d262746, d279640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d262746, d279640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro70369 (p : Pattern) (ha : d262752 p = 1) (hb : d279646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262747 q = 1) (hb : d279641 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d262747, d279641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262747, d279641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70368 q ha hb
  have h2 (q : Pattern) (ha : d262748 q = 1) (hb : d279642 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d262748, d279642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262748, d279642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d262749 q = 1) (hb : d279643 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d262749, d279643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262749, d279643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d262750 q = 1) (hb : d279644 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d262750, d279644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262750, d279644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d262751 q = 1) (hb : d279645 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d262751, d279645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262751, d279645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d262752 q = 1) (hb : d279646 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d262752, d279646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262752, d279646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70370 (p : Pattern) (ha : d262965 p = 1) (hb : d278575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262872 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262881 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d262945 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d262846 q = 1) (hb : d278570 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262846, d278570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70117 q ha hb
    | true =>
      simp only [d262846, d278570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70118 q ha hb
  have h5 (q : Pattern) (ha : d262946 q = 1) (hb : d278571 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262946, d278571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d262946, d278571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d262961 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d262962 q = 1) (hb : d278572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262962, d278572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d262962, d278572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d262963 q = 1) (hb : d278573 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262963, d278573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262963, d278573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d262964 q = 1) (hb : d278574 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262964, d278574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262964, d278574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d262965 q = 1) (hb : d278575 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262965, d278575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262965, d278575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro70371 (p : Pattern) (ha : d262986 p = 1) (hb : d278585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262872 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262881 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262945 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262846 q = 1) (hb : d278570 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262846, d278570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70117 q ha hb
    | true =>
      simp only [d262846, d278570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70118 q ha hb
  have h4 (q : Pattern) (ha : d262946 q = 1) (hb : d278571 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262946, d278571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262946, d278571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d262961 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d262962 q = 1) (hb : d278572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262962, d278572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d262962, d278572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d262963 q = 1) (hb : d278573 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262963, d278573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262963, d278573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262964 q = 1) (hb : d278574 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262964, d278574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262964, d278574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d262971 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d262976 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d262978 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d262856 q = 1) (hb : d278580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262856, d278580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70120 q ha hb
    | true =>
      simp only [d262856, d278580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70121 q ha hb
  have h13 (q : Pattern) (ha : d262979 q = 1) (hb : d278581 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262979, d278581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d262979, d278581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262982 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262983 q = 1) (hb : d278582 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262983, d278582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262983, d278582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262984 q = 1) (hb : d278583 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262984, d278583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d262984, d278583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d262985 q = 1) (hb : d278584 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262985, d278584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d262985, d278584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d262986 q = 1) (hb : d278585 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262986, d278585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d262986, d278585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro70372 (p : Pattern) (ha : d263006 p = 1) (hb : d279651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262856 q = 1) (hb : d278580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262856, d278580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70120 q ha hb
    | true =>
      simp only [d262856, d278580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70121 q ha hb
  have h3 (q : Pattern) (ha : d262979 q = 1) (hb : d278581 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262979, d278581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262979, d278581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262982 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262983 q = 1) (hb : d278582 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262983, d278582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262983, d278582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263004 q = 1) (hb : d278583 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263004, d278583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263004, d278583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263005 q = 1) (hb : d278584 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263005, d278584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263005, d278584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263006 q = 1) (hb : d279651 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263006, d279651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263006, d279651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70373 (p : Pattern) (ha : d263127 p = 1) (hb : d279662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263102 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263107 q = 1) (hb : d279657 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263107, d279657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70160 q ha hb
    | true =>
      simp only [d263107, d279657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70165 q ha hb
  have h3 (q : Pattern) (ha : d263108 q = 1) (hb : d279658 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263108, d279658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263108, d279658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263123 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263124 q = 1) (hb : d279659 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263124, d279659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263124, d279659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263125 q = 1) (hb : d279660 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263125, d279660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263125, d279660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263126 q = 1) (hb : d279661 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263126, d279661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263126, d279661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263127 q = 1) (hb : d279662 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263127, d279662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263127, d279662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70374 (p : Pattern) (ha : d263140 p = 1) (hb : d279668 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262987 q = 1) (hb : d278586 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262987, d278586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70370 q ha hb
    | true =>
      simp only [d262987, d278586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70371 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263000 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263001 q = 1) (hb : d278587 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263001, d278587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263001, d278587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263002 q = 1) (hb : d279649 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263002, d279649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263002, d279649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263003 q = 1) (hb : d279650 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263003, d279650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263003, d279650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263007 q = 1) (hb : d279652 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263007, d279652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263007, d279652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70372 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d263009 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d263010 q = 1) (hb : d279653 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263010, d279653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263010, d279653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d263011 q = 1) (hb : d279654 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263011, d279654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263011, d279654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d263012 q = 1) (hb : d279655 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263012, d279655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263012, d279655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d263013 q = 1) (hb : d279656 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263013, d279656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263013, d279656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263128 q = 1) (hb : d279663 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263128, d279663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263128, d279663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70373 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263135 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263136 q = 1) (hb : d279664 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263136, d279664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263136, d279664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263137 q = 1) (hb : d279665 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263137, d279665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263137, d279665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d263138 q = 1) (hb : d279666 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263138, d279666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263138, d279666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d263139 q = 1) (hb : d279667 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263139, d279667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263139, d279667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d263140 q = 1) (hb : d279668 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d263140, d279668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263140, d279668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro70375 (p : Pattern) (ha : d263146 p = 1) (hb : d279674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263141 q = 1) (hb : d279669 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d263141, d279669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263141, d279669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70374 q ha hb
  have h2 (q : Pattern) (ha : d263142 q = 1) (hb : d279670 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d263142, d279670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263142, d279670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263143 q = 1) (hb : d279671 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d263143, d279671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263143, d279671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263144 q = 1) (hb : d279672 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d263144, d279672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263144, d279672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263145 q = 1) (hb : d279673 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d263145, d279673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263145, d279673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263146 q = 1) (hb : d279674 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d263146, d279674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263146, d279674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70376 (p : Pattern) (ha : d263364 p = 1) (hb : d278939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263276 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263285 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d263331 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d263250 q = 1) (hb : d278934 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263250, d278934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70184 q ha hb
    | true =>
      simp only [d263250, d278934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70185 q ha hb
  have h5 (q : Pattern) (ha : d263332 q = 1) (hb : d278935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263332, d278935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d263332, d278935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d263360 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d263361 q = 1) (hb : d278936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263361, d278936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263361, d278936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d263362 q = 1) (hb : d278937 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263362, d278937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d263362, d278937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263363 q = 1) (hb : d278938 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263363, d278938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263363, d278938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263364 q = 1) (hb : d278939 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263364, d278939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263364, d278939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro70377 (p : Pattern) (ha : d263385 p = 1) (hb : d278949 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263276 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263285 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263331 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263250 q = 1) (hb : d278934 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263250, d278934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70184 q ha hb
    | true =>
      simp only [d263250, d278934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70185 q ha hb
  have h4 (q : Pattern) (ha : d263332 q = 1) (hb : d278935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263332, d278935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d263332, d278935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d263360 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d263361 q = 1) (hb : d278936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263361, d278936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263361, d278936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d263362 q = 1) (hb : d278937 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263362, d278937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263362, d278937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263363 q = 1) (hb : d278938 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263363, d278938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263363, d278938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d263370 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d263375 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d263377 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d263260 q = 1) (hb : d278944 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263260, d278944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70187 q ha hb
    | true =>
      simp only [d263260, d278944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70188 q ha hb
  have h13 (q : Pattern) (ha : d263378 q = 1) (hb : d278945 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263378, d278945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d263378, d278945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263381 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263382 q = 1) (hb : d278946 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263382, d278946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263382, d278946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263383 q = 1) (hb : d278947 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263383, d278947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d263383, d278947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d263384 q = 1) (hb : d278948 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263384, d278948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d263384, d278948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d263385 q = 1) (hb : d278949 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263385, d278949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263385, d278949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro70378 (p : Pattern) (ha : d263405 p = 1) (hb : d279680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263377 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263260 q = 1) (hb : d278944 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263260, d278944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70187 q ha hb
    | true =>
      simp only [d263260, d278944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70188 q ha hb
  have h3 (q : Pattern) (ha : d263378 q = 1) (hb : d278945 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263378, d278945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263378, d278945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263381 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263382 q = 1) (hb : d278946 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263382, d278946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263382, d278946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263403 q = 1) (hb : d278947 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263403, d278947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263403, d278947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263404 q = 1) (hb : d278948 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263404, d278948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263404, d278948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263405 q = 1) (hb : d279680 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263405, d279680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263405, d279680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70379 (p : Pattern) (ha : d263537 p = 1) (hb : d279691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263501 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263506 q = 1) (hb : d279686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263506, d279686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70228 q ha hb
    | true =>
      simp only [d263506, d279686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70234 q ha hb
  have h3 (q : Pattern) (ha : d263507 q = 1) (hb : d279687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263507, d279687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263507, d279687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263533 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263534 q = 1) (hb : d279688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263534, d279688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263534, d279688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263535 q = 1) (hb : d279689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263535, d279689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263535, d279689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263536 q = 1) (hb : d279690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263536, d279690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263536, d279690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263537 q = 1) (hb : d279691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263537, d279691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263537, d279691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70380 (p : Pattern) (ha : d263550 p = 1) (hb : d279697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263268 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263386 q = 1) (hb : d278950 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263386, d278950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70376 q ha hb
    | true =>
      simp only [d263386, d278950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70377 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263399 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263400 q = 1) (hb : d278951 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263400, d278951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263400, d278951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263401 q = 1) (hb : d279678 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263401, d279678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263401, d279678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263402 q = 1) (hb : d279679 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263402, d279679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263402, d279679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263406 q = 1) (hb : d279681 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263406, d279681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263406, d279681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70378 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d263408 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d263409 q = 1) (hb : d279682 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263409, d279682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263409, d279682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d263410 q = 1) (hb : d279683 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263410, d279683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263410, d279683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d263411 q = 1) (hb : d279684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263411, d279684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263411, d279684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d263412 q = 1) (hb : d279685 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263412, d279685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263412, d279685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263538 q = 1) (hb : d279692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263538, d279692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263538, d279692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70379 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263545 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263546 q = 1) (hb : d279693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263546, d279693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263546, d279693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263547 q = 1) (hb : d279694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263547, d279694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263547, d279694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d263548 q = 1) (hb : d279695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263548, d279695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263548, d279695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d263549 q = 1) (hb : d279696 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263549, d279696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263549, d279696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d263550 q = 1) (hb : d279697 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d263550, d279697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263550, d279697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro70381 (p : Pattern) (ha : d263556 p = 1) (hb : d279703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263551 q = 1) (hb : d279698 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d263551, d279698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263551, d279698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70380 q ha hb
  have h2 (q : Pattern) (ha : d263552 q = 1) (hb : d279699 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d263552, d279699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263552, d279699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263553 q = 1) (hb : d279700 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d263553, d279700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263553, d279700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263554 q = 1) (hb : d279701 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d263554, d279701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263554, d279701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263555 q = 1) (hb : d279702 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d263555, d279702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263555, d279702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263556 q = 1) (hb : d279703 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d263556, d279703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263556, d279703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70382 (p : Pattern) (ha : d263768 p = 1) (hb : d279276 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263690 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263699 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d263727 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d263664 q = 1) (hb : d279271 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263664, d279271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70253 q ha hb
    | true =>
      simp only [d263664, d279271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70254 q ha hb
  have h5 (q : Pattern) (ha : d263728 q = 1) (hb : d279272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263728, d279272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d263728, d279272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d263764 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d263765 q = 1) (hb : d279273 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263765, d279273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263765, d279273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d263766 q = 1) (hb : d279274 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263766, d279274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d263766, d279274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263767 q = 1) (hb : d279275 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263767, d279275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263767, d279275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263768 q = 1) (hb : d279276 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263768, d279276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263768, d279276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro70383 (p : Pattern) (ha : d263790 p = 1) (hb : d279286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263690 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263699 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263727 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263664 q = 1) (hb : d279271 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263664, d279271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70253 q ha hb
    | true =>
      simp only [d263664, d279271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70254 q ha hb
  have h4 (q : Pattern) (ha : d263728 q = 1) (hb : d279272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263728, d279272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d263728, d279272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d263764 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d263765 q = 1) (hb : d279273 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263765, d279273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263765, d279273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d263766 q = 1) (hb : d279274 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263766, d279274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263766, d279274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263767 q = 1) (hb : d279275 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263767, d279275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263767, d279275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d263774 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d263779 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d263782 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d263674 q = 1) (hb : d279281 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263674, d279281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70256 q ha hb
    | true =>
      simp only [d263674, d279281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70257 q ha hb
  have h13 (q : Pattern) (ha : d263783 q = 1) (hb : d279282 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263783, d279282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d263783, d279282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263786 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263787 q = 1) (hb : d279283 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263787, d279283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263787, d279283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263788 q = 1) (hb : d279284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263788, d279284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d263788, d279284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d263789 q = 1) (hb : d279285 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263789, d279285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d263789, d279285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d263790 q = 1) (hb : d279286 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263790, d279286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263790, d279286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro70384 (p : Pattern) (ha : d263815 p = 1) (hb : d279710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263782 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263674 q = 1) (hb : d279281 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263674, d279281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70256 q ha hb
    | true =>
      simp only [d263674, d279281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70257 q ha hb
  have h3 (q : Pattern) (ha : d263783 q = 1) (hb : d279282 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263783, d279282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263783, d279282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263786 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263787 q = 1) (hb : d279283 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263787, d279283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263787, d279283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263813 q = 1) (hb : d279284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263813, d279284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263813, d279284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263814 q = 1) (hb : d279285 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263814, d279285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263814, d279285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263815 q = 1) (hb : d279710 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263815, d279710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263815, d279710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70385 (p : Pattern) (ha : d263905 p = 1) (hb : d279717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263863 q = 1) (hb : d279437 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263863, d279437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70287 q ha hb
    | true =>
      simp only [d263863, d279437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70289 q ha hb
  have h2 (q : Pattern) (ha : d263864 q = 1) (hb : d279438 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263864, d279438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263864, d279438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263865 q = 1) (hb : d279439 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263865, d279439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263865, d279439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263872 q = 1) (hb : d279446 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263872, d279446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70289 q ha hb
    | true =>
      simp only [d263872, d279446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70290 q ha hb
  have h5 (q : Pattern) (ha : d263873 q = 1) (hb : d279447 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263873, d279447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263873, d279447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263874 q = 1) (hb : d279448 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263874, d279448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263874, d279448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263875 q = 1) (hb : d279449 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263875, d279449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263875, d279449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263891 q = 1) (hb : d279465 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263891, d279465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70289 q ha hb
    | true =>
      simp only [d263891, d279465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70294 q ha hb
  have h9 (q : Pattern) (ha : d263892 q = 1) (hb : d279466 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263892, d279466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263892, d279466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263893 q = 1) (hb : d279467 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263893, d279467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263893, d279467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263894 q = 1) (hb : d279468 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263894, d279468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263894, d279468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d263904 q = 1) (hb : d279716 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263904, d279716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263904, d279716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263905 q = 1) (hb : d279717 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263905, d279717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263905, d279717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro70386 (p : Pattern) (ha : d263911 p = 1) (hb : d279723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263906 q = 1) (hb : d279718 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263906, d279718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70385 q ha hb
    | true =>
      simp only [d263906, d279718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263907 q = 1) (hb : d279719 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263907, d279719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263907, d279719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263897 q = 1) (hb : d279471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263897, d279471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70295 q ha hb
    | true =>
      simp only [d263897, d279471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263898 q = 1) (hb : d279472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263898, d279472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263898, d279472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263908 q = 1) (hb : d279720 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263908, d279720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263908, d279720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263909 q = 1) (hb : d279721 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263909, d279721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263909, d279721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263910 q = 1) (hb : d279722 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263910, d279722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263910, d279722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263911 q = 1) (hb : d279723 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263911, d279723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263911, d279723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro70387 (p : Pattern) (ha : d263922 p = 1) (hb : d270515 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5238 q = 1) (hb : d53337 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5238, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15103 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263917 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5239 q = 1) (hb : d263918 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d263918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5239, d263918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27181 q = 1) (hb : d263919 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d27181, d263919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27181, d263919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2047 q = 1) (hb : d101726 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15103 q ha hb
    | true =>
      simp only [d2047, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2048 q = 1) (hb : d101728 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2048, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2061 q = 1) (hb : d101729 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2061, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27182 q = 1) (hb : d263920 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d27182, d263920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27182, d263920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27183 q = 1) (hb : d263921 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d27183, d263921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27183, d263921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d263922 q = 1) (hb : d270515 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d263922, d270515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d263922, d270515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro70388 (p : Pattern) (ha : d263928 p = 1) (hb : d279464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263857 q = 1) (hb : d279431 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263857, d279431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263857, d279431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70245 q ha hb
  have h2 (q : Pattern) (ha : d263616 q = 1) (hb : d279225 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263616, d279225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70245 q ha hb
    | true =>
      simp only [d263616, d279225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263858 q = 1) (hb : d279432 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263858, d279432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263858, d279432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263617 q = 1) (hb : d279226 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263617, d279226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263617, d279226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263859 q = 1) (hb : d279433 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263859, d279433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263859, d279433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263860 q = 1) (hb : d279434 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263860, d279434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263860, d279434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263889 q = 1) (hb : d279463 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263889, d279463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263889, d279463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123743 q = 1) (hb : d270722 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d123743, d270722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123743, d270722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70247 q ha hb
  have h9 (q : Pattern) (ha : d101733 q = 1) (hb : d270516 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d101733, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70247 q ha hb
    | true =>
      simp only [d101733, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d123744 q = 1) (hb : d270723 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d123744, d270723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123744, d270723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263923 q = 1) (hb : d270516 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263923, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70387 q ha hb
    | true =>
      simp only [d263923, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d263924 q = 1) (hb : d270517 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263924, d270517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263924, d270517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d263925 q = 1) (hb : d270724 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263925, d270724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263925, d270724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263926 q = 1) (hb : d270725 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263926, d270725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263926, d270725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d263927 q = 1) (hb : d270726 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263927, d270726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d263927, d270726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d263928 q = 1) (hb : d279464 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263928, d279464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263928, d279464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro70389 (p : Pattern) (ha : d263934 p = 1) (hb : d279470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263929 q = 1) (hb : d279465 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263929, d279465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70289 q ha hb
    | true =>
      simp only [d263929, d279465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70388 q ha hb
  have h2 (q : Pattern) (ha : d263930 q = 1) (hb : d279466 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263930, d279466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263930, d279466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263931 q = 1) (hb : d279467 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263931, d279467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263931, d279467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263932 q = 1) (hb : d279468 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263932, d279468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263932, d279468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263933 q = 1) (hb : d279469 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263933, d279469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263933, d279469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263934 q = 1) (hb : d279470 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263934, d279470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263934, d279470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70390 (p : Pattern) (ha : d263940 p = 1) (hb : d279502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263935 q = 1) (hb : d279471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263935, d279471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70389 q ha hb
    | true =>
      simp only [d263935, d279471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263936 q = 1) (hb : d279472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263936, d279472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263936, d279472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263937 q = 1) (hb : d279499 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263937, d279499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263937, d279499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263938 q = 1) (hb : d279500 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263938, d279500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263938, d279500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263939 q = 1) (hb : d279501 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263939, d279501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263939, d279501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263940 q = 1) (hb : d279502 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263940, d279502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263940, d279502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70391 (p : Pattern) (ha : d263972 p = 1) (hb : d279729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263903 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263941 q = 1) (hb : d279724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263941, d279724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70386 q ha hb
    | true =>
      simp only [d263941, d279724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70390 q ha hb
  have h3 (q : Pattern) (ha : d263942 q = 1) (hb : d279725 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263942, d279725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263942, d279725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263968 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263969 q = 1) (hb : d279726 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263969, d279726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263969, d279726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263970 q = 1) (hb : d279727 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263970, d279727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263970, d279727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263971 q = 1) (hb : d279728 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263971, d279728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263971, d279728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263972 q = 1) (hb : d279729 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263972, d279729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263972, d279729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70392 (p : Pattern) (ha : d263989 p = 1) (hb : d279735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263682 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263791 q = 1) (hb : d279287 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263791, d279287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70382 q ha hb
    | true =>
      simp only [d263791, d279287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70383 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263810 q = 1) (hb : d279288 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263810, d279288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263810, d279288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263811 q = 1) (hb : d279708 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263811, d279708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263811, d279708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263812 q = 1) (hb : d279709 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263812, d279709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263812, d279709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263816 q = 1) (hb : d279711 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263816, d279711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263816, d279711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70384 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d263818 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d263819 q = 1) (hb : d279712 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263819, d279712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263819, d279712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d263820 q = 1) (hb : d279713 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263820, d279713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263820, d279713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d263821 q = 1) (hb : d279714 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263821, d279714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263821, d279714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d263822 q = 1) (hb : d279715 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263822, d279715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263822, d279715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263973 q = 1) (hb : d279730 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263973, d279730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263973, d279730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70391 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263984 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263985 q = 1) (hb : d279731 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263985, d279731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263985, d279731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263986 q = 1) (hb : d279732 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263986, d279732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263986, d279732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d263987 q = 1) (hb : d279733 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263987, d279733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263987, d279733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d263988 q = 1) (hb : d279734 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263988, d279734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263988, d279734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d263989 q = 1) (hb : d279735 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d263989, d279735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263989, d279735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro70393 (p : Pattern) (ha : d263995 p = 1) (hb : d279741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263990 q = 1) (hb : d279736 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d263990, d279736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263990, d279736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70392 q ha hb
  have h2 (q : Pattern) (ha : d263991 q = 1) (hb : d279737 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d263991, d279737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263991, d279737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263992 q = 1) (hb : d279738 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d263992, d279738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263992, d279738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263993 q = 1) (hb : d279739 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d263993, d279739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263993, d279739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263994 q = 1) (hb : d279740 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d263994, d279740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263994, d279740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263995 q = 1) (hb : d279741 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d263995, d279741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263995, d279741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70394 (p : Pattern) (ha : d264001 p = 1) (hb : d279747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d262468 q = 1) (hb : d279620 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d262468, d279620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70357 q ha hb
    | true =>
      simp only [d262468, d279620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70363 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262753 q = 1) (hb : d279647 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d262753, d279647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262753, d279647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70369 q ha hb
  have h3 (q : Pattern) (ha : d262754 q = 1) (hb : d279648 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d262754, d279648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d262754, d279648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263147 q = 1) (hb : d279675 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d263147, d279675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263147, d279675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70375 q ha hb
  have h5 (q : Pattern) (ha : d263148 q = 1) (hb : d279676 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d263148, d279676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263148, d279676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263149 q = 1) (hb : d279677 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d263149, d279677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263149, d279677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263557 q = 1) (hb : d279704 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d263557, d279704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263557, d279704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70381 q ha hb
  have h8 (q : Pattern) (ha : d263558 q = 1) (hb : d279705 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d263558, d279705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263558, d279705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263559 q = 1) (hb : d279706 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d263559, d279706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263559, d279706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263560 q = 1) (hb : d279707 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d263560, d279707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263560, d279707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263996 q = 1) (hb : d279742 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d263996, d279742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263996, d279742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70393 q ha hb
  have h12 (q : Pattern) (ha : d263997 q = 1) (hb : d279743 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d263997, d279743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263997, d279743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263998 q = 1) (hb : d279744 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d263998, d279744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263998, d279744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263999 q = 1) (hb : d279745 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d263999, d279745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263999, d279745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d264000 q = 1) (hb : d279746 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d264000, d279746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d264000, d279746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d264001 q = 1) (hb : d279747 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d264001, d279747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d264001, d279747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro70395 (p : Pattern) (ha : d264007 p = 1) (hb : d279753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264002 q = 1) (hb : d279748 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d264002, d279748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70394 q ha hb
    | true =>
      simp only [d264002, d279748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264003 q = 1) (hb : d279749 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d264003, d279749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264003, d279749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264004 q = 1) (hb : d279750 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d264004, d279750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264004, d279750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264005 q = 1) (hb : d279751 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d264005, d279751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264005, d279751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264006 q = 1) (hb : d279752 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d264006, d279752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264006, d279752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264007 q = 1) (hb : d279753 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d264007, d279753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264007, d279753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70396 (p : Pattern) (ha : d264013 p = 1) (hb : d279759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264008 q = 1) (hb : d279754 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d264008, d279754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70395 q ha hb
    | true =>
      simp only [d264008, d279754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264009 q = 1) (hb : d279755 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d264009, d279755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264009, d279755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264010 q = 1) (hb : d279756 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d264010, d279756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264010, d279756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264011 q = 1) (hb : d279757 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d264011, d279757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264011, d279757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264012 q = 1) (hb : d279758 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d264012, d279758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264012, d279758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264013 q = 1) (hb : d279759 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d264013, d279759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264013, d279759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70397 (p : Pattern) (ha : d264019 p = 1) (hb : d279765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264014 q = 1) (hb : d279760 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d264014, d279760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70396 q ha hb
    | true =>
      simp only [d264014, d279760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264015 q = 1) (hb : d279761 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d264015, d279761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264015, d279761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264016 q = 1) (hb : d279762 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d264016, d279762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264016, d279762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264017 q = 1) (hb : d279763 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d264017, d279763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264017, d279763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264018 q = 1) (hb : d279764 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d264018, d279764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264018, d279764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264019 q = 1) (hb : d279765 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d264019, d279765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264019, d279765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70398 (p : Pattern) (ha : d264025 p = 1) (hb : d279771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264020 q = 1) (hb : d279766 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d264020, d279766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70397 q ha hb
    | true =>
      simp only [d264020, d279766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264021 q = 1) (hb : d279767 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d264021, d279767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264021, d279767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264022 q = 1) (hb : d279768 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d264022, d279768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264022, d279768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264023 q = 1) (hb : d279769 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d264023, d279769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264023, d279769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264024 q = 1) (hb : d279770 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d264024, d279770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264024, d279770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264025 q = 1) (hb : d279771 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d264025, d279771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264025, d279771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70399 (p : Pattern) (ha : d264031 p = 1) (hb : d279777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264026 q = 1) (hb : d279772 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d264026, d279772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70398 q ha hb
    | true =>
      simp only [d264026, d279772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264027 q = 1) (hb : d279773 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d264027, d279773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264027, d279773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264028 q = 1) (hb : d279774 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d264028, d279774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264028, d279774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264029 q = 1) (hb : d279775 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d264029, d279775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264029, d279775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264030 q = 1) (hb : d279776 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d264030, d279776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264030, d279776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264031 q = 1) (hb : d279777 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d264031, d279777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264031, d279777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70400 (p : Pattern) (ha : d264037 p = 1) (hb : d279783 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264032 q = 1) (hb : d279778 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d264032, d279778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70399 q ha hb
    | true =>
      simp only [d264032, d279778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264033 q = 1) (hb : d279779 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d264033, d279779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264033, d279779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264034 q = 1) (hb : d279780 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d264034, d279780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264034, d279780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264035 q = 1) (hb : d279781 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d264035, d279781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264035, d279781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264036 q = 1) (hb : d279782 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d264036, d279782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264036, d279782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264037 q = 1) (hb : d279783 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d264037, d279783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264037, d279783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70401 (p : Pattern) (ha : d264043 p = 1) (hb : d279789 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264038 q = 1) (hb : d279784 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d264038, d279784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70400 q ha hb
    | true =>
      simp only [d264038, d279784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264039 q = 1) (hb : d279785 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d264039, d279785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264039, d279785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264040 q = 1) (hb : d279786 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d264040, d279786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264040, d279786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264041 q = 1) (hb : d279787 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d264041, d279787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264041, d279787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264042 q = 1) (hb : d279788 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d264042, d279788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264042, d279788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264043 q = 1) (hb : d279789 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d264043, d279789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264043, d279789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro70402 (p : Pattern) (ha : d265953 p = 1) (hb : d277830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33319 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33325 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d33360 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d277766 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265949 q = 1) (hb : d277826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265949, d277826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d265949, d277826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d33394 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d265950 q = 1) (hb : d277827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265950, d277827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265950, d277827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d265951 q = 1) (hb : d277828 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265951, d277828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d265951, d277828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265952 q = 1) (hb : d277829 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265952, d277829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265952, d277829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265953 q = 1) (hb : d277830 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265953, d277830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265953, d277830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro70403 (p : Pattern) (ha : d265958 p = 1) (hb : d277837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33319 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33325 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33360 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d277766 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d265949 q = 1) (hb : d277826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265949, d277826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d265949, d277826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d33394 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d265950 q = 1) (hb : d277827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265950, d277827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265950, d277827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d265951 q = 1) (hb : d277828 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265951, d277828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265951, d277828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265952 q = 1) (hb : d277829 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265952, d277829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d265952, d277829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d33403 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d33407 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d33409 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d277773 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d265954 q = 1) (hb : d277833 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265954, d277833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d265954, d277833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d33415 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d265955 q = 1) (hb : d277834 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265955, d277834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265955, d277834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d265956 q = 1) (hb : d277835 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265956, d277835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d265956, d277835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d265957 q = 1) (hb : d277836 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265957, d277836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d265957, d277836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d265958 q = 1) (hb : d277837 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265958, d277837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265958, d277837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro70404 (p : Pattern) (ha : d265965 p = 1) (hb : d279571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33409 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d277773 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265954 q = 1) (hb : d277833 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265954, d277833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265954, d277833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33415 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265955 q = 1) (hb : d277834 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265955, d277834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265955, d277834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d265963 q = 1) (hb : d277835 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265963, d277835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265963, d277835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265964 q = 1) (hb : d277836 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265964, d277836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265964, d277836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265965 q = 1) (hb : d279571 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265965, d279571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265965, d279571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70405 (p : Pattern) (ha : d265975 p = 1) (hb : d279581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33457 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d277809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265971 q = 1) (hb : d279577 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265971, d279577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265971, d279577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33483 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265972 q = 1) (hb : d279578 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265972, d279578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265972, d279578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d265973 q = 1) (hb : d279579 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265973, d279579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265973, d279579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265974 q = 1) (hb : d279580 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265974, d279580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265974, d279580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265975 q = 1) (hb : d279581 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265975, d279581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265975, d279581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70406 (p : Pattern) (ha : d265981 p = 1) (hb : d279587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d265959 q = 1) (hb : d277838 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265959, d277838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70402 q ha hb
    | true =>
      simp only [d265959, d277838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70403 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33422 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265960 q = 1) (hb : d277839 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265960, d277839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265960, d277839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265961 q = 1) (hb : d279569 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265961, d279569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265961, d279569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265962 q = 1) (hb : d279570 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265962, d279570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d265962, d279570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265966 q = 1) (hb : d279572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265966, d279572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265966, d279572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70404 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d265967 q = 1) (hb : d279573 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265967, d279573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d265967, d279573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d265968 q = 1) (hb : d279574 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265968, d279574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265968, d279574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d265969 q = 1) (hb : d279575 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265969, d279575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d265969, d279575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d265970 q = 1) (hb : d279576 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265970, d279576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d265970, d279576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d265976 q = 1) (hb : d279582 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265976, d279582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265976, d279582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70405 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d265977 q = 1) (hb : d279583 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265977, d279583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265977, d279583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d265978 q = 1) (hb : d279584 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265978, d279584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d265978, d279584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d265979 q = 1) (hb : d279585 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265979, d279585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d265979, d279585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d265980 q = 1) (hb : d279586 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265980, d279586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d265980, d279586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d265981 q = 1) (hb : d279587 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d265981, d279587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d265981, d279587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro70407 (p : Pattern) (ha : d265987 p = 1) (hb : d279593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d265944 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d265944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d265944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66749 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d265945 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d265945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d265945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d265946 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d265946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d265946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d265947 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d265947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d265947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d265948 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d265948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d265948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265982 q = 1) (hb : d279588 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d265982, d279588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265982, d279588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70406 q ha hb
  have h8 (q : Pattern) (ha : d265983 q = 1) (hb : d279589 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d265983, d279589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265983, d279589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265984 q = 1) (hb : d279590 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d265984, d279590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265984, d279590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265985 q = 1) (hb : d279591 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d265985, d279591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265985, d279591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d265986 q = 1) (hb : d279592 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d265986, d279592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265986, d279592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d265987 q = 1) (hb : d279593 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d265987, d279593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d265987, d279593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro70408 (p : Pattern) (ha : d265992 p = 1) (hb : d278000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33543 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33552 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d33602 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d277995 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265988 q = 1) (hb : d277996 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265988, d277996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d265988, d277996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d33653 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d265989 q = 1) (hb : d277997 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265989, d277997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265989, d277997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d265990 q = 1) (hb : d277998 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265990, d277998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d265990, d277998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265991 q = 1) (hb : d277999 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265991, d277999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265991, d277999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265992 q = 1) (hb : d278000 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265992, d278000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265992, d278000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro70409 (p : Pattern) (ha : d265997 p = 1) (hb : d278010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33543 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33552 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33602 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d277995 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d265988 q = 1) (hb : d277996 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265988, d277996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d265988, d277996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d33653 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d265989 q = 1) (hb : d277997 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265989, d277997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265989, d277997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d265990 q = 1) (hb : d277998 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265990, d277998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265990, d277998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265991 q = 1) (hb : d277999 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265991, d277999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d265991, d277999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d33663 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d33668 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d33670 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d278005 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d265993 q = 1) (hb : d278006 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265993, d278006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d265993, d278006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d33677 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d265994 q = 1) (hb : d278007 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265994, d278007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265994, d278007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d265995 q = 1) (hb : d278008 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265995, d278008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d265995, d278008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d265996 q = 1) (hb : d278009 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265996, d278009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d265996, d278009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d265997 q = 1) (hb : d278010 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265997, d278010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265997, d278010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro70410 (p : Pattern) (ha : d266004 p = 1) (hb : d279596 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33670 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d278005 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265993 q = 1) (hb : d278006 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265993, d278006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265993, d278006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33677 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265994 q = 1) (hb : d278007 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265994, d278007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265994, d278007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266002 q = 1) (hb : d278008 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266002, d278008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266002, d278008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266003 q = 1) (hb : d278009 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266003, d278009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266003, d278009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266004 q = 1) (hb : d279596 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266004, d279596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266004, d279596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70411 (p : Pattern) (ha : d266014 p = 1) (hb : d279607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d279602 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266010 q = 1) (hb : d279603 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266010, d279603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266010, d279603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33793 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266011 q = 1) (hb : d279604 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266011, d279604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266011, d279604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266012 q = 1) (hb : d279605 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266012, d279605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266012, d279605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266013 q = 1) (hb : d279606 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266013, d279606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266013, d279606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266014 q = 1) (hb : d279607 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266014, d279607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266014, d279607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70412 (p : Pattern) (ha : d266020 p = 1) (hb : d279613 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33535 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d265998 q = 1) (hb : d278011 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265998, d278011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70408 q ha hb
    | true =>
      simp only [d265998, d278011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70409 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33695 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265999 q = 1) (hb : d278012 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265999, d278012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265999, d278012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266000 q = 1) (hb : d279594 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266000, d279594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266000, d279594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266001 q = 1) (hb : d279595 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266001, d279595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266001, d279595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266005 q = 1) (hb : d279597 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266005, d279597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266005, d279597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70410 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d33704 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266006 q = 1) (hb : d279598 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266006, d279598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266006, d279598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266007 q = 1) (hb : d279599 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266007, d279599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266007, d279599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266008 q = 1) (hb : d279600 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266008, d279600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266008, d279600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266009 q = 1) (hb : d279601 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266009, d279601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266009, d279601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266015 q = 1) (hb : d279608 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266015, d279608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266015, d279608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70411 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d33809 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266016 q = 1) (hb : d279609 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266016, d279609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266016, d279609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266017 q = 1) (hb : d279610 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266017, d279610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266017, d279610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266018 q = 1) (hb : d279611 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266018, d279611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266018, d279611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266019 q = 1) (hb : d279612 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266019, d279612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266019, d279612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266020 q = 1) (hb : d279613 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266020, d279613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266020, d279613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro70413 (p : Pattern) (ha : d266026 p = 1) (hb : d279619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266021 q = 1) (hb : d279614 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266021, d279614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266021, d279614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70412 q ha hb
  have h2 (q : Pattern) (ha : d266022 q = 1) (hb : d279615 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266022, d279615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266022, d279615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266023 q = 1) (hb : d279616 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266023, d279616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266023, d279616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266024 q = 1) (hb : d279617 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266024, d279617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266024, d279617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266025 q = 1) (hb : d279618 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266025, d279618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266025, d279618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266026 q = 1) (hb : d279619 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266026, d279619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266026, d279619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70414 (p : Pattern) (ha : d266032 p = 1) (hb : d278250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33883 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33892 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d33949 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d278245 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266028 q = 1) (hb : d278246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266028, d278246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d266028, d278246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d34023 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d266029 q = 1) (hb : d278247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266029, d278247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266029, d278247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d266030 q = 1) (hb : d278248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266030, d278248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266030, d278248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266031 q = 1) (hb : d278249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266031, d278249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266031, d278249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266032 q = 1) (hb : d278250 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266032, d278250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266032, d278250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro70415 (p : Pattern) (ha : d266037 p = 1) (hb : d278260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33883 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33892 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33949 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d278245 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d266028 q = 1) (hb : d278246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266028, d278246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266028, d278246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d34023 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d266029 q = 1) (hb : d278247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266029, d278247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266029, d278247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d266030 q = 1) (hb : d278248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266030, d278248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266030, d278248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266031 q = 1) (hb : d278249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266031, d278249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266031, d278249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d34033 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d34038 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d34040 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d278255 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d266033 q = 1) (hb : d278256 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266033, d278256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d266033, d278256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d34047 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266034 q = 1) (hb : d278257 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266034, d278257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266034, d278257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266035 q = 1) (hb : d278258 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266035, d278258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d266035, d278258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d266036 q = 1) (hb : d278259 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266036, d278259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d266036, d278259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d266037 q = 1) (hb : d278260 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266037, d278260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266037, d278260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro70416 (p : Pattern) (ha : d266044 p = 1) (hb : d279623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34040 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d278255 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266033 q = 1) (hb : d278256 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266033, d278256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266033, d278256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d34047 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266034 q = 1) (hb : d278257 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266034, d278257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266034, d278257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266042 q = 1) (hb : d278258 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266042, d278258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266042, d278258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266043 q = 1) (hb : d278259 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266043, d278259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266043, d278259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266044 q = 1) (hb : d279623 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266044, d279623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266044, d279623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70417 (p : Pattern) (ha : d266054 p = 1) (hb : d279634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34140 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d279629 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266050 q = 1) (hb : d279630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266050, d279630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266050, d279630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d34195 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266051 q = 1) (hb : d279631 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266051, d279631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266051, d279631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266052 q = 1) (hb : d279632 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266052, d279632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266052, d279632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266053 q = 1) (hb : d279633 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266053, d279633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266053, d279633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266054 q = 1) (hb : d279634 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266054, d279634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266054, d279634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70418 (p : Pattern) (ha : d266060 p = 1) (hb : d279640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266038 q = 1) (hb : d278261 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266038, d278261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70414 q ha hb
    | true =>
      simp only [d266038, d278261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70415 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34065 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266039 q = 1) (hb : d278262 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266039, d278262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266039, d278262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266040 q = 1) (hb : d279621 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266040, d279621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266040, d279621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266041 q = 1) (hb : d279622 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266041, d279622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266041, d279622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266045 q = 1) (hb : d279624 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266045, d279624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266045, d279624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70416 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d34074 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266046 q = 1) (hb : d279625 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266046, d279625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266046, d279625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266047 q = 1) (hb : d279626 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266047, d279626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266047, d279626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266048 q = 1) (hb : d279627 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266048, d279627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266048, d279627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266049 q = 1) (hb : d279628 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266049, d279628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266049, d279628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266055 q = 1) (hb : d279635 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266055, d279635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266055, d279635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70417 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d34211 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266056 q = 1) (hb : d279636 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266056, d279636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266056, d279636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266057 q = 1) (hb : d279637 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266057, d279637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266057, d279637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266058 q = 1) (hb : d279638 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266058, d279638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266058, d279638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266059 q = 1) (hb : d279639 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266059, d279639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266059, d279639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266060 q = 1) (hb : d279640 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266060, d279640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266060, d279640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro70419 (p : Pattern) (ha : d266066 p = 1) (hb : d279646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266061 q = 1) (hb : d279641 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266061, d279641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266061, d279641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70418 q ha hb
  have h2 (q : Pattern) (ha : d266062 q = 1) (hb : d279642 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266062, d279642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266062, d279642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266063 q = 1) (hb : d279643 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266063, d279643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266063, d279643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266064 q = 1) (hb : d279644 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266064, d279644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266064, d279644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266065 q = 1) (hb : d279645 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266065, d279645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266065, d279645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266066 q = 1) (hb : d279646 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266066, d279646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266066, d279646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70420 (p : Pattern) (ha : d266073 p = 1) (hb : d278575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34342 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d34415 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d278570 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266069 q = 1) (hb : d278571 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266069, d278571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d266069, d278571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d34534 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d266070 q = 1) (hb : d278572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266070, d278572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266070, d278572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d266071 q = 1) (hb : d278573 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266071, d278573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266071, d278573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266072 q = 1) (hb : d278574 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266072, d278574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266072, d278574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266073 q = 1) (hb : d278575 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266073, d278575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266073, d278575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro70421 (p : Pattern) (ha : d266078 p = 1) (hb : d278585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d34342 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34351 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34415 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d278570 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d266069 q = 1) (hb : d278571 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266069, d278571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266069, d278571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d34534 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d266070 q = 1) (hb : d278572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266070, d278572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266070, d278572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d266071 q = 1) (hb : d278573 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266071, d278573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266071, d278573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266072 q = 1) (hb : d278574 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266072, d278574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266072, d278574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d34544 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d34549 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d34551 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d278580 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d266074 q = 1) (hb : d278581 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266074, d278581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d266074, d278581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d34558 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266075 q = 1) (hb : d278582 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266075, d278582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266075, d278582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266076 q = 1) (hb : d278583 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266076, d278583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d266076, d278583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d266077 q = 1) (hb : d278584 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266077, d278584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d266077, d278584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d266078 q = 1) (hb : d278585 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266078, d278585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266078, d278585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro70422 (p : Pattern) (ha : d266085 p = 1) (hb : d279651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34551 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d278580 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266074 q = 1) (hb : d278581 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266074, d278581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266074, d278581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d34558 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266075 q = 1) (hb : d278582 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266075, d278582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266075, d278582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266083 q = 1) (hb : d278583 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266083, d278583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266083, d278583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266084 q = 1) (hb : d278584 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266084, d278584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266084, d278584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266085 q = 1) (hb : d279651 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266085, d279651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266085, d279651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70423 (p : Pattern) (ha : d266095 p = 1) (hb : d279662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34678 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d279657 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266091 q = 1) (hb : d279658 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266091, d279658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266091, d279658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d34751 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266092 q = 1) (hb : d279659 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266092, d279659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266092, d279659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266093 q = 1) (hb : d279660 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266093, d279660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266093, d279660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266094 q = 1) (hb : d279661 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266094, d279661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266094, d279661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266095 q = 1) (hb : d279662 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266095, d279662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266095, d279662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70424 (p : Pattern) (ha : d266101 p = 1) (hb : d279668 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d34334 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266079 q = 1) (hb : d278586 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266079, d278586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70420 q ha hb
    | true =>
      simp only [d266079, d278586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70421 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34576 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266080 q = 1) (hb : d278587 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266080, d278587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266080, d278587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266081 q = 1) (hb : d279649 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266081, d279649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266081, d279649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266082 q = 1) (hb : d279650 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266082, d279650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266082, d279650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266086 q = 1) (hb : d279652 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266086, d279652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266086, d279652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70422 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d34585 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266087 q = 1) (hb : d279653 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266087, d279653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266087, d279653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266088 q = 1) (hb : d279654 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266088, d279654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266088, d279654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266089 q = 1) (hb : d279655 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266089, d279655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266089, d279655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266090 q = 1) (hb : d279656 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266090, d279656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266090, d279656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266096 q = 1) (hb : d279663 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266096, d279663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266096, d279663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70423 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d34767 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266097 q = 1) (hb : d279664 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266097, d279664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266097, d279664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266098 q = 1) (hb : d279665 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266098, d279665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266098, d279665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266099 q = 1) (hb : d279666 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266099, d279666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266099, d279666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266100 q = 1) (hb : d279667 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266100, d279667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266100, d279667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266101 q = 1) (hb : d279668 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266101, d279668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266101, d279668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro70425 (p : Pattern) (ha : d266107 p = 1) (hb : d279674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266102 q = 1) (hb : d279669 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266102, d279669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266102, d279669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70424 q ha hb
  have h2 (q : Pattern) (ha : d266103 q = 1) (hb : d279670 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266103, d279670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266103, d279670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266104 q = 1) (hb : d279671 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266104, d279671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266104, d279671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266105 q = 1) (hb : d279672 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266105, d279672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266105, d279672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266106 q = 1) (hb : d279673 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266106, d279673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266106, d279673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266107 q = 1) (hb : d279674 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266107, d279674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266107, d279674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70426 (p : Pattern) (ha : d266115 p = 1) (hb : d278939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34908 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34917 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d34963 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d278934 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266111 q = 1) (hb : d278935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266111, d278935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d266111, d278935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d35102 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d266112 q = 1) (hb : d278936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266112, d278936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266112, d278936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d266113 q = 1) (hb : d278937 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266113, d278937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266113, d278937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266114 q = 1) (hb : d278938 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266114, d278938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266114, d278938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266115 q = 1) (hb : d278939 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266115, d278939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266115, d278939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro70427 (p : Pattern) (ha : d266120 p = 1) (hb : d278949 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d34908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34917 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34963 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d278934 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d266111 q = 1) (hb : d278935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266111, d278935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266111, d278935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d35102 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d266112 q = 1) (hb : d278936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266112, d278936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266112, d278936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d266113 q = 1) (hb : d278937 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266113, d278937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266113, d278937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266114 q = 1) (hb : d278938 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266114, d278938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266114, d278938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d35112 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d35117 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d35119 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d278944 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d266116 q = 1) (hb : d278945 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266116, d278945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d266116, d278945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d35126 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266117 q = 1) (hb : d278946 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266117, d278946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266117, d278946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266118 q = 1) (hb : d278947 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266118, d278947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d266118, d278947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d266119 q = 1) (hb : d278948 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266119, d278948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d266119, d278948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d266120 q = 1) (hb : d278949 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266120, d278949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266120, d278949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro70428 (p : Pattern) (ha : d266127 p = 1) (hb : d279680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35119 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d278944 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266116 q = 1) (hb : d278945 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266116, d278945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266116, d278945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d35126 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266117 q = 1) (hb : d278946 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266117, d278946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266117, d278946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266125 q = 1) (hb : d278947 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266125, d278947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266125, d278947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266126 q = 1) (hb : d278948 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266126, d278948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266126, d278948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266127 q = 1) (hb : d279680 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266127, d279680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266127, d279680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70429 (p : Pattern) (ha : d266137 p = 1) (hb : d279691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35246 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d279686 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266133 q = 1) (hb : d279687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266133, d279687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266133, d279687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d35330 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266134 q = 1) (hb : d279688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266134, d279688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266134, d279688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266135 q = 1) (hb : d279689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266135, d279689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266135, d279689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266136 q = 1) (hb : d279690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266136, d279690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266136, d279690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266137 q = 1) (hb : d279691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266137, d279691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266137, d279691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70430 (p : Pattern) (ha : d266143 p = 1) (hb : d279697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d34900 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266121 q = 1) (hb : d278950 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266121, d278950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70426 q ha hb
    | true =>
      simp only [d266121, d278950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70427 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d35144 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266122 q = 1) (hb : d278951 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266122, d278951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266122, d278951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266123 q = 1) (hb : d279678 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266123, d279678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266123, d279678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266124 q = 1) (hb : d279679 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266124, d279679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266124, d279679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266128 q = 1) (hb : d279681 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266128, d279681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266128, d279681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70428 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d35153 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266129 q = 1) (hb : d279682 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266129, d279682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266129, d279682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266130 q = 1) (hb : d279683 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266130, d279683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266130, d279683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266131 q = 1) (hb : d279684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266131, d279684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266131, d279684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266132 q = 1) (hb : d279685 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266132, d279685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266132, d279685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266138 q = 1) (hb : d279692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266138, d279692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266138, d279692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70429 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d35346 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266139 q = 1) (hb : d279693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266139, d279693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266139, d279693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266140 q = 1) (hb : d279694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266140, d279694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266140, d279694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266141 q = 1) (hb : d279695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266141, d279695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266141, d279695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266142 q = 1) (hb : d279696 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266142, d279696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266142, d279696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266143 q = 1) (hb : d279697 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266143, d279697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266143, d279697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro70431 (p : Pattern) (ha : d266149 p = 1) (hb : d279703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266144 q = 1) (hb : d279698 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266144, d279698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266144, d279698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70430 q ha hb
  have h2 (q : Pattern) (ha : d266145 q = 1) (hb : d279699 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266145, d279699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266145, d279699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266146 q = 1) (hb : d279700 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266146, d279700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266146, d279700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266147 q = 1) (hb : d279701 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266147, d279701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266147, d279701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266148 q = 1) (hb : d279702 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266148, d279702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266148, d279702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266149 q = 1) (hb : d279703 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266149, d279703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266149, d279703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70432 (p : Pattern) (ha : d266158 p = 1) (hb : d279276 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35491 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d35500 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d35528 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d279271 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266154 q = 1) (hb : d279272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266154, d279272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d266154, d279272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d35669 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d266155 q = 1) (hb : d279273 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266155, d279273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266155, d279273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d266156 q = 1) (hb : d279274 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266156, d279274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266156, d279274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266157 q = 1) (hb : d279275 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266157, d279275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266157, d279275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266158 q = 1) (hb : d279276 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266158, d279276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266158, d279276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro70433 (p : Pattern) (ha : d266163 p = 1) (hb : d279286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d35491 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35500 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d35528 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d279271 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d266154 q = 1) (hb : d279272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266154, d279272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266154, d279272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d35669 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d266155 q = 1) (hb : d279273 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266155, d279273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266155, d279273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d266156 q = 1) (hb : d279274 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266156, d279274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266156, d279274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266157 q = 1) (hb : d279275 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266157, d279275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266157, d279275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d35679 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d35684 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d35687 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d279281 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d266159 q = 1) (hb : d279282 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266159, d279282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d266159, d279282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d35694 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266160 q = 1) (hb : d279283 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266160, d279283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266160, d279283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266161 q = 1) (hb : d279284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266161, d279284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d266161, d279284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d266162 q = 1) (hb : d279285 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266162, d279285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d266162, d279285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d266163 q = 1) (hb : d279286 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266163, d279286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266163, d279286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro70434 (p : Pattern) (ha : d266170 p = 1) (hb : d279710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35687 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d279281 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266159 q = 1) (hb : d279282 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266159, d279282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266159, d279282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d35694 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266160 q = 1) (hb : d279283 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266160, d279283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266160, d279283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266168 q = 1) (hb : d279284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266168, d279284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266168, d279284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266169 q = 1) (hb : d279285 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266169, d279285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266169, d279285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266170 q = 1) (hb : d279710 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266170, d279710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266170, d279710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70435 (p : Pattern) (ha : d266180 p = 1) (hb : d279729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35811 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d279724 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266176 q = 1) (hb : d279725 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266176, d279725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266176, d279725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d35929 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266177 q = 1) (hb : d279726 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266177, d279726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266177, d279726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266178 q = 1) (hb : d279727 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266178, d279727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266178, d279727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266179 q = 1) (hb : d279728 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266179, d279728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266179, d279728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266180 q = 1) (hb : d279729 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266180, d279729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266180, d279729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70436 (p : Pattern) (ha : d266186 p = 1) (hb : d279735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d35483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266164 q = 1) (hb : d279287 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266164, d279287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70432 q ha hb
    | true =>
      simp only [d266164, d279287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70433 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d35717 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266165 q = 1) (hb : d279288 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266165, d279288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266165, d279288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266166 q = 1) (hb : d279708 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266166, d279708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266166, d279708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266167 q = 1) (hb : d279709 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266167, d279709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266167, d279709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266171 q = 1) (hb : d279711 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266171, d279711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266171, d279711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70434 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d35726 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266172 q = 1) (hb : d279712 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266172, d279712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266172, d279712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266173 q = 1) (hb : d279713 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266173, d279713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266173, d279713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266174 q = 1) (hb : d279714 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266174, d279714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266174, d279714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266175 q = 1) (hb : d279715 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266175, d279715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266175, d279715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266181 q = 1) (hb : d279730 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266181, d279730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266181, d279730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70435 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d35945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266182 q = 1) (hb : d279731 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266182, d279731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266182, d279731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266183 q = 1) (hb : d279732 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266183, d279732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266183, d279732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266184 q = 1) (hb : d279733 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266184, d279733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266184, d279733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266185 q = 1) (hb : d279734 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266185, d279734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266185, d279734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266186 q = 1) (hb : d279735 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266186, d279735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266186, d279735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro70437 (p : Pattern) (ha : d266192 p = 1) (hb : d279741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266187 q = 1) (hb : d279736 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266187, d279736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266187, d279736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70436 q ha hb
  have h2 (q : Pattern) (ha : d266188 q = 1) (hb : d279737 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266188, d279737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266188, d279737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266189 q = 1) (hb : d279738 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266189, d279738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266189, d279738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266190 q = 1) (hb : d279739 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266190, d279739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266190, d279739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266191 q = 1) (hb : d279740 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266191, d279740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266191, d279740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266192 q = 1) (hb : d279741 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266192, d279741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266192, d279741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70438 (p : Pattern) (ha : d266198 p = 1) (hb : d279747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d266027 q = 1) (hb : d279620 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266027, d279620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70407 q ha hb
    | true =>
      simp only [d266027, d279620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70413 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d266067 q = 1) (hb : d279647 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266067, d279647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266067, d279647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70419 q ha hb
  have h3 (q : Pattern) (ha : d266068 q = 1) (hb : d279648 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d266068, d279648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266068, d279648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266108 q = 1) (hb : d279675 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266108, d279675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266108, d279675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70425 q ha hb
  have h5 (q : Pattern) (ha : d266109 q = 1) (hb : d279676 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d266109, d279676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266109, d279676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266110 q = 1) (hb : d279677 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d266110, d279677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266110, d279677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266150 q = 1) (hb : d279704 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266150, d279704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266150, d279704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70431 q ha hb
  have h8 (q : Pattern) (ha : d266151 q = 1) (hb : d279705 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d266151, d279705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266151, d279705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266152 q = 1) (hb : d279706 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d266152, d279706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266152, d279706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266153 q = 1) (hb : d279707 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d266153, d279707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266153, d279707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d266193 q = 1) (hb : d279742 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266193, d279742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266193, d279742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70437 q ha hb
  have h12 (q : Pattern) (ha : d266194 q = 1) (hb : d279743 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d266194, d279743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266194, d279743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266195 q = 1) (hb : d279744 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d266195, d279744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266195, d279744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d266196 q = 1) (hb : d279745 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d266196, d279745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266196, d279745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d266197 q = 1) (hb : d279746 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d266197, d279746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266197, d279746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d266198 q = 1) (hb : d279747 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d266198, d279747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266198, d279747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro70439 (p : Pattern) (ha : d266204 p = 1) (hb : d279753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266199 q = 1) (hb : d279748 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d266199, d279748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70438 q ha hb
    | true =>
      simp only [d266199, d279748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266200 q = 1) (hb : d279749 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d266200, d279749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266200, d279749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266201 q = 1) (hb : d279750 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d266201, d279750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266201, d279750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266202 q = 1) (hb : d279751 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d266202, d279751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266202, d279751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266203 q = 1) (hb : d279752 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d266203, d279752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266203, d279752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266204 q = 1) (hb : d279753 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d266204, d279753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266204, d279753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro70440 (p : Pattern) (ha : d266210 p = 1) (hb : d279759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266205 q = 1) (hb : d279754 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d266205, d279754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70439 q ha hb
    | true =>
      simp only [d266205, d279754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266206 q = 1) (hb : d279755 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d266206, d279755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266206, d279755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266207 q = 1) (hb : d279756 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d266207, d279756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266207, d279756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266208 q = 1) (hb : d279757 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d266208, d279757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266208, d279757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266209 q = 1) (hb : d279758 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d266209, d279758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266209, d279758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266210 q = 1) (hb : d279759 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d266210, d279759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266210, d279759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro70441 (p : Pattern) (ha : d266216 p = 1) (hb : d279765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266211 q = 1) (hb : d279760 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d266211, d279760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70440 q ha hb
    | true =>
      simp only [d266211, d279760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266212 q = 1) (hb : d279761 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d266212, d279761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266212, d279761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266213 q = 1) (hb : d279762 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d266213, d279762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266213, d279762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266214 q = 1) (hb : d279763 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d266214, d279763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266214, d279763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266215 q = 1) (hb : d279764 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d266215, d279764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266215, d279764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266216 q = 1) (hb : d279765 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d266216, d279765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266216, d279765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro70442 (p : Pattern) (ha : d266222 p = 1) (hb : d279771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266217 q = 1) (hb : d279766 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d266217, d279766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70441 q ha hb
    | true =>
      simp only [d266217, d279766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266218 q = 1) (hb : d279767 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d266218, d279767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266218, d279767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266219 q = 1) (hb : d279768 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d266219, d279768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266219, d279768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266220 q = 1) (hb : d279769 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d266220, d279769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266220, d279769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266221 q = 1) (hb : d279770 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d266221, d279770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266221, d279770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266222 q = 1) (hb : d279771 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d266222, d279771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266222, d279771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro70443 (p : Pattern) (ha : d266228 p = 1) (hb : d279777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266223 q = 1) (hb : d279772 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d266223, d279772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70442 q ha hb
    | true =>
      simp only [d266223, d279772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266224 q = 1) (hb : d279773 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d266224, d279773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266224, d279773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266225 q = 1) (hb : d279774 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d266225, d279774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266225, d279774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266226 q = 1) (hb : d279775 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d266226, d279775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266226, d279775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266227 q = 1) (hb : d279776 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d266227, d279776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266227, d279776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266228 q = 1) (hb : d279777 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d266228, d279777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266228, d279777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro70444 (p : Pattern) (ha : d266234 p = 1) (hb : d279783 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266229 q = 1) (hb : d279778 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d266229, d279778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70443 q ha hb
    | true =>
      simp only [d266229, d279778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266230 q = 1) (hb : d279779 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d266230, d279779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266230, d279779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266231 q = 1) (hb : d279780 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d266231, d279780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266231, d279780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266232 q = 1) (hb : d279781 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d266232, d279781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266232, d279781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266233 q = 1) (hb : d279782 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d266233, d279782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266233, d279782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266234 q = 1) (hb : d279783 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d266234, d279783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266234, d279783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro70445 (p : Pattern) (ha : d266240 p = 1) (hb : d279789 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266235 q = 1) (hb : d279784 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d266235, d279784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70444 q ha hb
    | true =>
      simp only [d266235, d279784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266236 q = 1) (hb : d279785 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d266236, d279785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266236, d279785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266237 q = 1) (hb : d279786 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d266237, d279786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266237, d279786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266238 q = 1) (hb : d279787 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d266238, d279787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266238, d279787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266239 q = 1) (hb : d279788 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d266239, d279788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266239, d279788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266240 q = 1) (hb : d279789 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d266240, d279789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266240, d279789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro70446 (p : Pattern) (ha : d15966 p = 1) (hb : d236582 p = 1) : d23236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d236582 q = 1) : d23231 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57476 q ha hb
    | true =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d236582 q = 1) : d23232 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d236582 q = 1) : d23233 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d23233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d23233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d236582 q = 1) : d23234 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d23234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d23234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139 q = 1) (hb : d236582 q = 1) : d9382 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57458 q ha hb
    | true =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d140 q = 1) (hb : d236582 q = 1) : d9384 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d141 q = 1) (hb : d236582 q = 1) : d12493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d142 q = 1) (hb : d236582 q = 1) : d12494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d142, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d323 q = 1) (hb : d236582 q = 1) : d23235 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d23235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d323, d23235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12495 q = 1) (hb : d236582 q = 1) : d12495 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15966 q = 1) (hb : d236582 q = 1) : d23236 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15966, d23236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15966, d23236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro70447 (p : Pattern) (ha : d15972 p = 1) (hb : d236582 p = 1) : d23242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d236582 q = 1) : d23237 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d23237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70446 q ha hb
    | true =>
      simp only [d15967, d23237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57459 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d236582 q = 1) : d23238 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d23238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d23238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d236582 q = 1) : d23239 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d23239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d23239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d236582 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d236582 q = 1) : d23135 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57459 q ha hb
    | true =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d236582 q = 1) : d23136 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d236582 q = 1) : d23137 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15970 q = 1) (hb : d236582 q = 1) : d23240 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d23240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d23240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d236582 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d148 q = 1) (hb : d236582 q = 1) : d23138 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d23138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148, d23138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15971 q = 1) (hb : d236582 q = 1) : d23241 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15971, d23241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15971, d23241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15972 q = 1) (hb : d236582 q = 1) : d23242 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15972, d23242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15972, d23242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro70448 (p : Pattern) (ha : d15978 p = 1) (hb : d236582 p = 1) : d23248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d236582 q = 1) : d23243 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d23243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70447 q ha hb
    | true =>
      simp only [d15973, d23243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d236582 q = 1) : d23244 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d23244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d23244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d236582 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57460 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d236582 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d236582 q = 1) : d23245 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d23245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d23245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d236582 q = 1) : d23246 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d23246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d23246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d236582 q = 1) : d23247 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d23247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d23247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15978 q = 1) (hb : d236582 q = 1) : d23248 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15978, d23248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15978, d23248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70449 (p : Pattern) (ha : d128195 p = 1) (hb : d236582 p = 1) : d211124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d236582 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d236582 q = 1) : d23218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d23218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57474 q ha hb
    | true =>
      simp only [d297, d23218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d236582 q = 1) : d23219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d23219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d23219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d236582 q = 1) : d23220 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d23220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d23220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d236582 q = 1) : d23221 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d23221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d23221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d236582 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d236582 q = 1) : d23225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d23225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57475 q ha hb
    | true =>
      simp only [d304, d23225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d236582 q = 1) : d23226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d23226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d23226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d236582 q = 1) : d23227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d23227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d23227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15979 q = 1) (hb : d236582 q = 1) : d23249 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d23249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70448 q ha hb
    | true =>
      simp only [d15979, d23249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57467 q ha hb
  have h11 (q : Pattern) (ha : d128191 q = 1) (hb : d236582 q = 1) : d211120 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d211120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128191, d211120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d236582 q = 1) : d23269 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d23269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57480 q ha hb
    | true =>
      simp only [d4737, d23269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d236582 q = 1) : d23270 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d23270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d23270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d128192 q = 1) (hb : d236582 q = 1) : d211121 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d211121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128192, d211121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128193 q = 1) (hb : d236582 q = 1) : d211122 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d211122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128193, d211122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128194 q = 1) (hb : d236582 q = 1) : d211123 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d211123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128194, d211123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128195 q = 1) (hb : d236582 q = 1) : d211124 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128195, d211124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128195, d211124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro70450 (p : Pattern) (ha : d15985 p = 1) (hb : d236582 p = 1) : d23284 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d236582 q = 1) : d23243 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d23243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70447 q ha hb
    | true =>
      simp only [d15973, d23243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d236582 q = 1) : d23244 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d23244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d23244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d236582 q = 1) : d23141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57460 q ha hb
    | true =>
      simp only [d151, d23141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d236582 q = 1) : d23142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d23142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d236582 q = 1) : d23245 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d23245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d23245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d236582 q = 1) : d23246 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d23246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d23246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d236582 q = 1) : d23247 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d23247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d23247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15985 q = 1) (hb : d236582 q = 1) : d23284 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15985, d23284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15985, d23284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro70451 (p : Pattern) (ha : d128200 p = 1) (hb : d236582 p = 1) : d211129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d236582 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d236582 q = 1) : d23218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d23218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57474 q ha hb
    | true =>
      simp only [d297, d23218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d236582 q = 1) : d23219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d23219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d23219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d236582 q = 1) : d23220 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d23220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d23220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d236582 q = 1) : d23221 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d23221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d23221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d236582 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d236582 q = 1) : d23225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d23225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57475 q ha hb
    | true =>
      simp only [d304, d23225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d236582 q = 1) : d23226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d23226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d23226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d236582 q = 1) : d23227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d23227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d23227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15979 q = 1) (hb : d236582 q = 1) : d23249 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d23249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70448 q ha hb
    | true =>
      simp only [d15979, d23249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57467 q ha hb
  have h11 (q : Pattern) (ha : d128191 q = 1) (hb : d236582 q = 1) : d211120 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d211120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128191, d211120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d236582 q = 1) : d23269 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d23269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57480 q ha hb
    | true =>
      simp only [d4737, d23269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d236582 q = 1) : d23270 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d23270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d23270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d128192 q = 1) (hb : d236582 q = 1) : d211121 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d211121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128192, d211121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128193 q = 1) (hb : d236582 q = 1) : d211122 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d211122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128193, d211122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128194 q = 1) (hb : d236582 q = 1) : d211123 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d211123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128194, d211123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d236582 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d377 q = 1) (hb : d236582 q = 1) : d23276 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d23276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57482 q ha hb
    | true =>
      simp only [d377, d23276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d378 q = 1) (hb : d236582 q = 1) : d23277 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d23277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d378, d23277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d379 q = 1) (hb : d236582 q = 1) : d23278 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d23278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d379, d23278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d380 q = 1) (hb : d236582 q = 1) : d23279 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d23279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d23279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d236582 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d382 q = 1) (hb : d236582 q = 1) : d23281 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d23281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57483 q ha hb
    | true =>
      simp only [d382, d23281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d383 q = 1) (hb : d236582 q = 1) : d23282 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d23282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d383, d23282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d384 q = 1) (hb : d236582 q = 1) : d23283 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d23283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d384, d23283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d15986 q = 1) (hb : d236582 q = 1) : d23285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d23285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70450 q ha hb
    | true =>
      simp only [d15986, d23285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57461 q ha hb
  have h27 (q : Pattern) (ha : d128196 q = 1) (hb : d236582 q = 1) : d211125 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d211125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d128196, d211125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d5356 q = 1) (hb : d236582 q = 1) : d23290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d23290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57485 q ha hb
    | true =>
      simp only [d5356, d23290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d5357 q = 1) (hb : d236582 q = 1) : d23291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d23291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d5357, d23291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d128197 q = 1) (hb : d236582 q = 1) : d211126 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d211126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d128197, d211126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d128198 q = 1) (hb : d236582 q = 1) : d211127 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128198, d211127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d128198, d211127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d128199 q = 1) (hb : d236582 q = 1) : d211128 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128199, d211128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128199, d211128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d128200 q = 1) (hb : d236582 q = 1) : d211129 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128200, d211129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128200, d211129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro70452 (p : Pattern) (ha : d128207 p = 1) (hb : d236582 p = 1) : d211136 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15986 q = 1) (hb : d236582 q = 1) : d23285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d23285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70450 q ha hb
    | true =>
      simp only [d15986, d23285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57461 q ha hb
  have h2 (q : Pattern) (ha : d128196 q = 1) (hb : d236582 q = 1) : d211125 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d211125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128196, d211125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d236582 q = 1) : d23290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d23290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57485 q ha hb
    | true =>
      simp only [d5356, d23290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5357 q = 1) (hb : d236582 q = 1) : d23291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d23291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5357, d23291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128197 q = 1) (hb : d236582 q = 1) : d211126 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d211126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128197, d211126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128205 q = 1) (hb : d236582 q = 1) : d211134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128205, d211134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128205, d211134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128206 q = 1) (hb : d236582 q = 1) : d211135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128206, d211135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128206, d211135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128207 q = 1) (hb : d236582 q = 1) : d211136 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128207, d211136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128207, d211136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70453 (p : Pattern) (ha : d16004 p = 1) (hb : d236582 p = 1) : d23315 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d236582 q = 1) : d23310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d23310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d23310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57476 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d236582 q = 1) : d23231 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57476 q ha hb
    | true =>
      simp only [d319, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d236582 q = 1) : d23311 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d23311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d23311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d236582 q = 1) : d23232 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d236582 q = 1) : d23312 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d23312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d23312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d236582 q = 1) : d23313 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d23313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d23313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d226 q = 1) (hb : d236582 q = 1) : d12599 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d12599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d12599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57458 q ha hb
  have h8 (q : Pattern) (ha : d139 q = 1) (hb : d236582 q = 1) : d9382 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57458 q ha hb
    | true =>
      simp only [d139, d9382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d227 q = 1) (hb : d236582 q = 1) : d12600 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d12600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d227, d12600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d140 q = 1) (hb : d236582 q = 1) : d9384 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140, d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d228 q = 1) (hb : d236582 q = 1) : d12601 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d12601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d228, d12601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d229 q = 1) (hb : d236582 q = 1) : d12602 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d12602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d229, d12602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d416 q = 1) (hb : d236582 q = 1) : d23314 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d23314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d416, d23314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12603 q = 1) (hb : d236582 q = 1) : d12603 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d16004 q = 1) (hb : d236582 q = 1) : d23315 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16004, d23315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16004, d23315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro70454 (p : Pattern) (ha : d16010 p = 1) (hb : d236582 p = 1) : d23321 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d236582 q = 1) : d23316 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d23316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70453 q ha hb
    | true =>
      simp only [d16005, d23316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57463 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d236582 q = 1) : d23317 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d23317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d23317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d236582 q = 1) : d23318 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d23318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d23318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d236582 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d236582 q = 1) : d23172 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d23172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57463 q ha hb
    | true =>
      simp only [d232, d23172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d236582 q = 1) : d23173 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d23173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d23173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d236582 q = 1) : d23174 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d23174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d23174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d236582 q = 1) : d23319 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d23319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d23319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d236582 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d235 q = 1) (hb : d236582 q = 1) : d23175 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d23175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d235, d23175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16009 q = 1) (hb : d236582 q = 1) : d23320 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16009, d23320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16009, d23320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16010 q = 1) (hb : d236582 q = 1) : d23321 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16010, d23321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16010, d23321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro70455 (p : Pattern) (ha : d16016 p = 1) (hb : d236582 p = 1) : d23327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16011 q = 1) (hb : d236582 q = 1) : d23322 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16011, d23322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70454 q ha hb
    | true =>
      simp only [d16011, d23322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16012 q = 1) (hb : d236582 q = 1) : d23323 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16012, d23323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16012, d23323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238 q = 1) (hb : d236582 q = 1) : d23178 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d23178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57464 q ha hb
    | true =>
      simp only [d238, d23178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239 q = 1) (hb : d236582 q = 1) : d23179 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d23179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d23179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16013 q = 1) (hb : d236582 q = 1) : d23324 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16013, d23324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16013, d23324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16014 q = 1) (hb : d236582 q = 1) : d23325 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16014, d23325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16014, d23325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16015 q = 1) (hb : d236582 q = 1) : d23326 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16015, d23326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16015, d23326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16016 q = 1) (hb : d236582 q = 1) : d23327 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16016, d23327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16016, d23327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro70456 (p : Pattern) (ha : d128217 p = 1) (hb : d236582 p = 1) : d211146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16017 q = 1) (hb : d236582 q = 1) : d23328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16017, d23328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70455 q ha hb
    | true =>
      simp only [d16017, d23328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57465 q ha hb
  have h2 (q : Pattern) (ha : d128213 q = 1) (hb : d236582 q = 1) : d211142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128213, d211142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128213, d211142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d236582 q = 1) : d23348 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d23348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57491 q ha hb
    | true =>
      simp only [d5378, d23348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d236582 q = 1) : d23349 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d23349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5379, d23349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128214 q = 1) (hb : d236582 q = 1) : d211143 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128214, d211143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128214, d211143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128215 q = 1) (hb : d236582 q = 1) : d211144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128215, d211144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128215, d211144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128216 q = 1) (hb : d236582 q = 1) : d211145 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128216, d211145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128216, d211145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128217 q = 1) (hb : d236582 q = 1) : d211146 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128217, d211146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128217, d211146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70457 (p : Pattern) (ha : d128223 p = 1) (hb : d236582 p = 1) : d211152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d236582 q = 1) : d23206 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d23206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d23206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57471 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d236582 q = 1) : d23207 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d23207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d23207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d236582 q = 1) : d23213 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d23213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57471 q ha hb
    | true =>
      simp only [d292, d23213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57472 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d236582 q = 1) : d23214 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d23214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d23214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d236582 q = 1) : d23215 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d23215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d23215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128201 q = 1) (hb : d236582 q = 1) : d211130 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128201, d211130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70449 q ha hb
    | true =>
      simp only [d128201, d211130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70451 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d236582 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d398 q = 1) (hb : d236582 q = 1) : d23298 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d23298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57473 q ha hb
    | true =>
      simp only [d398, d23298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128202 q = 1) (hb : d236582 q = 1) : d211131 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128202, d211131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128202, d211131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128203 q = 1) (hb : d236582 q = 1) : d211132 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128203, d211132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128203, d211132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d128204 q = 1) (hb : d236582 q = 1) : d211133 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128204, d211133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128204, d211133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128208 q = 1) (hb : d236582 q = 1) : d211137 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128208, d211137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128208, d211137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70452 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d236582 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d128209 q = 1) (hb : d236582 q = 1) : d211138 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128209, d211138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128209, d211138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128210 q = 1) (hb : d236582 q = 1) : d211139 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128210, d211139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128210, d211139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128211 q = 1) (hb : d236582 q = 1) : d211140 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128211, d211140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128211, d211140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d128212 q = 1) (hb : d236582 q = 1) : d211141 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128212, d211141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128212, d211141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d128218 q = 1) (hb : d236582 q = 1) : d211147 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128218, d211147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128218, d211147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70456 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d236582 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d128219 q = 1) (hb : d236582 q = 1) : d211148 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128219, d211148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128219, d211148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d128220 q = 1) (hb : d236582 q = 1) : d211149 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128220, d211149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128220, d211149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128221 q = 1) (hb : d236582 q = 1) : d211150 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128221, d211150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128221, d211150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128222 q = 1) (hb : d236582 q = 1) : d211151 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128222, d211151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128222, d211151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d128223 q = 1) (hb : d236582 q = 1) : d211152 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128223, d211152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128223, d211152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro70458 (p : Pattern) (ha : d128229 p = 1) (hb : d236582 p = 1) : d211158 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d236582 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d236582 q = 1) : d211115 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d211115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d211115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57470 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d236582 q = 1) : d211116 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d211116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d211116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d236582 q = 1) : d211117 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d211117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d211117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d236582 q = 1) : d211118 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d211118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d211118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d236582 q = 1) : d211119 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d211119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51657, d211119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128224 q = 1) (hb : d236582 q = 1) : d211153 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128224, d211153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128224, d211153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70457 q ha hb
  have h8 (q : Pattern) (ha : d128225 q = 1) (hb : d236582 q = 1) : d211154 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128225, d211154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128225, d211154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128226 q = 1) (hb : d236582 q = 1) : d211155 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128226, d211155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128226, d211155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128227 q = 1) (hb : d236582 q = 1) : d211156 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128227, d211156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128227, d211156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128228 q = 1) (hb : d236582 q = 1) : d211157 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128228, d211157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128228, d211157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128229 q = 1) (hb : d236582 q = 1) : d211158 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128229, d211158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128229, d211158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro70459 (p : Pattern) (ha : d16036 p = 1) (hb : d236582 p = 1) : d23368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d236582 q = 1) : d23237 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d23237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70446 q ha hb
    | true =>
      simp only [d15967, d23237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57459 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d236582 q = 1) : d23238 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d23238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d23238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d236582 q = 1) : d23239 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d23239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d23239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d236582 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d236582 q = 1) : d23135 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57459 q ha hb
    | true =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d236582 q = 1) : d23136 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d236582 q = 1) : d23137 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15970 q = 1) (hb : d236582 q = 1) : d23240 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d23240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d23240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d475 q = 1) (hb : d236582 q = 1) : d23366 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d23366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d475, d23366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16035 q = 1) (hb : d236582 q = 1) : d23367 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16035, d23367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16035, d23367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16036 q = 1) (hb : d236582 q = 1) : d23368 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16036, d23368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16036, d23368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro70460 (p : Pattern) (ha : d16042 p = 1) (hb : d236582 p = 1) : d23378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d236582 q = 1) : d23369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70459 q ha hb
    | true =>
      simp only [d16037, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d236582 q = 1) : d23370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d236582 q = 1) : d23373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57496 q ha hb
    | true =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d236582 q = 1) : d23374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d236582 q = 1) : d23375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d236582 q = 1) : d23376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d23376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d23376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d236582 q = 1) : d23377 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d23377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d23377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16042 q = 1) (hb : d236582 q = 1) : d23378 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16042, d23378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16042, d23378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70461 (p : Pattern) (ha : d16048 p = 1) (hb : d236582 p = 1) : d23388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d236582 q = 1) : d23383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d23383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70460 q ha hb
    | true =>
      simp only [d16043, d23383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57498 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d236582 q = 1) : d23384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d23384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d23384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d236582 q = 1) : d23385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d23385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d23385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d236582 q = 1) : d23386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d23386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d23386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d236582 q = 1) : d23387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d23387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d23387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16048 q = 1) (hb : d236582 q = 1) : d23388 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16048, d23388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16048, d23388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70462 (p : Pattern) (ha : d16051 p = 1) (hb : d236582 p = 1) : d23391 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d236582 q = 1) : d23369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70459 q ha hb
    | true =>
      simp only [d16037, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d236582 q = 1) : d23370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d236582 q = 1) : d23373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57496 q ha hb
    | true =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d236582 q = 1) : d23374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d236582 q = 1) : d23375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d236582 q = 1) : d23376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d23376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d23376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d236582 q = 1) : d23377 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d23377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d23377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16051 q = 1) (hb : d236582 q = 1) : d23391 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16051, d23391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16051, d23391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro70463 (p : Pattern) (ha : d16057 p = 1) (hb : d236582 p = 1) : d23398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d236582 q = 1) : d23383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d23383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70460 q ha hb
    | true =>
      simp only [d16043, d23383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57498 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d236582 q = 1) : d23384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d23384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d23384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d236582 q = 1) : d23385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d23385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d23385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d236582 q = 1) : d23386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d23386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d23386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d236582 q = 1) : d23387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d23387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d23387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16052 q = 1) (hb : d236582 q = 1) : d23393 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d23393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70462 q ha hb
    | true =>
      simp only [d16052, d23393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57501 q ha hb
  have h7 (q : Pattern) (ha : d16053 q = 1) (hb : d236582 q = 1) : d23394 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d23394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, d23394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16054 q = 1) (hb : d236582 q = 1) : d23395 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d23395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16054, d23395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16055 q = 1) (hb : d236582 q = 1) : d23396 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d23396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d23396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16056 q = 1) (hb : d236582 q = 1) : d23397 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d23397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d23397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16057 q = 1) (hb : d236582 q = 1) : d23398 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16057, d23398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16057, d23398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro70464 (p : Pattern) (ha : d16143 p = 1) (hb : d236582 p = 1) : d23513 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d236582 q = 1) : d23383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d23383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70460 q ha hb
    | true =>
      simp only [d16043, d23383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57498 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d236582 q = 1) : d23384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d23384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d23384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d236582 q = 1) : d23385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d23385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d23385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d236582 q = 1) : d23386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d23386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d23386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d236582 q = 1) : d23387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d23387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d23387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d236582 q = 1) : d23508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d23508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57498 q ha hb
    | true =>
      simp only [d633, d23508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d236582 q = 1) : d23509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d23509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d23509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d236582 q = 1) : d23510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d23510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d23510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d236582 q = 1) : d23511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d23511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d23511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d236582 q = 1) : d23512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d23512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d23512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16143 q = 1) (hb : d236582 q = 1) : d23513 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16143, d23513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16143, d23513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro70465 (p : Pattern) (ha : d16062 p = 1) (hb : d236582 p = 1) : d23403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d236582 q = 1) : d23369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70459 q ha hb
    | true =>
      simp only [d16037, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d236582 q = 1) : d23370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d236582 q = 1) : d23373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57496 q ha hb
    | true =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d236582 q = 1) : d23374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d236582 q = 1) : d23375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d236582 q = 1) : d23376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d23376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d23376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d236582 q = 1) : d23402 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d23402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d23402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16062 q = 1) (hb : d236582 q = 1) : d23403 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16062, d23403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16062, d23403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70466 (p : Pattern) (ha : d16069 p = 1) (hb : d236582 p = 1) : d23412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d236582 q = 1) : d23369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70459 q ha hb
    | true =>
      simp only [d16037, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d236582 q = 1) : d23370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d236582 q = 1) : d23373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57496 q ha hb
    | true =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d236582 q = 1) : d23374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d236582 q = 1) : d23375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d236582 q = 1) : d23410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d23410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d23410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d236582 q = 1) : d23411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d23411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d23411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16069 q = 1) (hb : d236582 q = 1) : d23412 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16069, d23412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16069, d23412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70467 (p : Pattern) (ha : d16114 p = 1) (hb : d236582 p = 1) : d23476 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d236582 q = 1) : d23369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70459 q ha hb
    | true =>
      simp only [d16037, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d236582 q = 1) : d23370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d236582 q = 1) : d23473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d23473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d23473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d236582 q = 1) : d23474 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d23474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d23474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d236582 q = 1) : d23475 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d23475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d23475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16114 q = 1) (hb : d236582 q = 1) : d23476 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16114, d23476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16114, d23476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70468 (p : Pattern) (ha : d28745 p = 1) (hb : d236582 p = 1) : d23421 p = 1 := by
  have h0 (q : Pattern) (ha : d533 q = 1) (hb : d236581 q = 1) : d533 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28742 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d28743 q = 1) (hb : d236582 q = 1) : d23419 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d28743, d236582, d23419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28743, d236582, d23419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d28744 q = 1) (hb : d236582 q = 1) : d23420 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28744, d23420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28744, d23420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315 q = 1) (hb : d236581 q = 1) : d315 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d135 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d316 q = 1) (hb : d236582 q = 1) : d23228 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d236582, d23228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316, d236582, d23228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d317 q = 1) (hb : d236582 q = 1) : d23229 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d23229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d317, d23229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d28745 q = 1) (hb : d236582 q = 1) : d23421 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28745, d23421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28745, d23421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro70469 (p : Pattern) (ha : d28750 p = 1) (hb : d236582 p = 1) : d23230 p = 1 := by
  have h0 (q : Pattern) (ha : d315 q = 1) (hb : d236581 q = 1) : d315 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d316 q = 1) (hb : d236582 q = 1) : d23228 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d236582, d23228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d316, d236582, d23228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d317 q = 1) (hb : d236582 q = 1) : d23229 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d23229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d317, d23229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5449 q = 1) (hb : d236582 q = 1) : d5449 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d28750 q = 1) (hb : d236582 q = 1) : d23230 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28750, d23230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28750, d23230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70470 (p : Pattern) (ha : d28756 p = 1) (hb : d236582 p = 1) : d23427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28746 q = 1) (hb : d236582 q = 1) : d23422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70468 q ha hb
    | true =>
      simp only [d28746, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28747 q = 1) (hb : d236582 q = 1) : d23423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28747, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28748 q = 1) (hb : d236582 q = 1) : d23424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28748, d23424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28748, d23424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28749 q = 1) (hb : d236582 q = 1) : d23425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28749, d23425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28749, d23425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28751 q = 1) (hb : d236582 q = 1) : d23231 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28751, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70469 q ha hb
    | true =>
      simp only [d28751, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28752 q = 1) (hb : d236582 q = 1) : d23232 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28752, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28752, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28753 q = 1) (hb : d236582 q = 1) : d23233 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28753, d23233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28753, d23233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28754 q = 1) (hb : d236582 q = 1) : d23234 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28754, d23234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28754, d23234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28755 q = 1) (hb : d236582 q = 1) : d23426 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28755, d23426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28755, d23426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23235 q = 1) (hb : d236582 q = 1) : d23235 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d28756 q = 1) (hb : d236582 q = 1) : d23427 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28756, d23427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28756, d23427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro70471 (p : Pattern) (ha : d28762 p = 1) (hb : d236582 p = 1) : d23433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28757 q = 1) (hb : d236582 q = 1) : d23428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28757, d23428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70470 q ha hb
    | true =>
      simp only [d28757, d23428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70446 q ha hb
  have h2 (q : Pattern) (ha : d28758 q = 1) (hb : d236582 q = 1) : d23429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28758, d23429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28758, d23429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28759 q = 1) (hb : d236582 q = 1) : d23430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28759, d23430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28759, d23430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16081 q = 1) (hb : d236582 q = 1) : d16081 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16082 q = 1) (hb : d236582 q = 1) : d23237 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16082, d23237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70446 q ha hb
    | true =>
      simp only [d16082, d23237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16083 q = 1) (hb : d236582 q = 1) : d23238 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16083, d23238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16083, d23238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16084 q = 1) (hb : d236582 q = 1) : d23239 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16084, d23239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16084, d23239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28760 q = 1) (hb : d236582 q = 1) : d23431 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28760, d23431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28760, d23431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15967 q = 1) (hb : d236582 q = 1) : d23237 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d23237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70446 q ha hb
    | true =>
      simp only [d15967, d23237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57459 q ha hb
  have h10 (q : Pattern) (ha : d15968 q = 1) (hb : d236582 q = 1) : d23238 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d23238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d23238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15969 q = 1) (hb : d236582 q = 1) : d23239 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d23239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d23239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30 q = 1) (hb : d236582 q = 1) : d30 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d145 q = 1) (hb : d236582 q = 1) : d23135 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57459 q ha hb
    | true =>
      simp only [d145, d23135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146 q = 1) (hb : d236582 q = 1) : d23136 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d23136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147 q = 1) (hb : d236582 q = 1) : d23137 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d23137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15970 q = 1) (hb : d236582 q = 1) : d23240 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d23240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15970, d23240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28761 q = 1) (hb : d236582 q = 1) : d23432 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28761, d23432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28761, d23432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d28762 q = 1) (hb : d236582 q = 1) : d23433 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28762, d23433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d28762, d23433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h18 p ha hb
theorem andIntro70472 (p : Pattern) (ha : d28768 p = 1) (hb : d236582 p = 1) : d23439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28763 q = 1) (hb : d236582 q = 1) : d23434 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28763, d23434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70471 q ha hb
    | true =>
      simp only [d28763, d23434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28764 q = 1) (hb : d236582 q = 1) : d23435 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28764, d23435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28764, d23435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d236582 q = 1) : d23369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70459 q ha hb
    | true =>
      simp only [d16037, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d236582 q = 1) : d23370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28765 q = 1) (hb : d236582 q = 1) : d23436 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28765, d23436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28765, d23436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28766 q = 1) (hb : d236582 q = 1) : d23437 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28766, d23437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28766, d23437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28767 q = 1) (hb : d236582 q = 1) : d23438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28767, d23438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28767, d23438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28768 q = 1) (hb : d236582 q = 1) : d23439 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28768, d23439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28768, d23439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70473 (p : Pattern) (ha : d236582 p = 1) (hb : d238875 p = 1) : d211163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d236582 q = 1) : d23406 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d23406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70465 q ha hb
    | true =>
      simp only [d16063, d23406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57510 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d236582 q = 1) : d23407 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d23407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d23407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d236582 q = 1) : d23408 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d23408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d23408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d236582 q = 1) : d23409 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d23409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d23409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d236582 q = 1) : d23416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d23416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70466 q ha hb
    | true =>
      simp only [d16070, d23416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57512 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d236582 q = 1) : d23417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d23417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d23417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d236582 q = 1) : d23418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d23418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d23418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28769 q = 1) (hb : d236582 q = 1) : d23440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28769, d23440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70472 q ha hb
    | true =>
      simp only [d28769, d23440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70460 q ha hb
  have h9 (q : Pattern) (ha : d236582 q = 1) (hb : d238871 q = 1) : d211159 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238871, d211159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d238871, d211159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d236582 q = 1) : d23477 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d23477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70467 q ha hb
    | true =>
      simp only [d16115, d23477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d236582 q = 1) : d23478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d23478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d23478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d236582 q = 1) (hb : d238872 q = 1) : d211160 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238872, d211160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238872, d211160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d236582 q = 1) (hb : d238873 q = 1) : d211161 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238873, d211161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d238873, d211161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d236582 q = 1) (hb : d238874 q = 1) : d211162 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238874, d211162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d238874, d211162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d236582 q = 1) (hb : d238875 q = 1) : d211163 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238875, d211163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238875, d211163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro70474 (p : Pattern) (ha : d16121 p = 1) (hb : d236582 p = 1) : d23483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d236582 q = 1) : d23369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70459 q ha hb
    | true =>
      simp only [d16037, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d236582 q = 1) : d23370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d236582 q = 1) : d23373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57496 q ha hb
    | true =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d236582 q = 1) : d23374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d236582 q = 1) : d23375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d236582 q = 1) : d23376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d23376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d23376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d236582 q = 1) : d23402 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d23402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d23402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16121 q = 1) (hb : d236582 q = 1) : d23483 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16121, d23483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16121, d23483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro70475 (p : Pattern) (ha : d16126 p = 1) (hb : d236582 p = 1) : d23489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d236582 q = 1) : d23369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70459 q ha hb
    | true =>
      simp only [d16037, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d236582 q = 1) : d23370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d236582 q = 1) : d23373 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57496 q ha hb
    | true =>
      simp only [d482, d23373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d236582 q = 1) : d23374 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d23374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d236582 q = 1) : d23375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d23375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d236582 q = 1) : d23410 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d23410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d23410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d236582 q = 1) : d23411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d23411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d23411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16126 q = 1) (hb : d236582 q = 1) : d23489 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16126, d23489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16126, d23489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro70476 (p : Pattern) (ha : d16135 p = 1) (hb : d236582 p = 1) : d23500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d236582 q = 1) : d23369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70459 q ha hb
    | true =>
      simp only [d16037, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d236582 q = 1) : d23370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d236582 q = 1) : d23473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d23473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d23473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d236582 q = 1) : d23474 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d23474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d23474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d236582 q = 1) : d23475 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d23475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d23475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16135 q = 1) (hb : d236582 q = 1) : d23500 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16135, d23500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16135, d23500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro70477 (p : Pattern) (ha : d28775 p = 1) (hb : d236582 p = 1) : d23494 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28763 q = 1) (hb : d236582 q = 1) : d23434 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28763, d23434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70471 q ha hb
    | true =>
      simp only [d28763, d23434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28764 q = 1) (hb : d236582 q = 1) : d23435 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28764, d23435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28764, d23435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d236582 q = 1) : d23369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70459 q ha hb
    | true =>
      simp only [d16037, d23369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d236582 q = 1) : d23370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d23370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28765 q = 1) (hb : d236582 q = 1) : d23436 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28765, d23436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28765, d23436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28766 q = 1) (hb : d236582 q = 1) : d23437 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28766, d23437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28766, d23437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28767 q = 1) (hb : d236582 q = 1) : d23438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28767, d23438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28767, d23438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28775 q = 1) (hb : d236582 q = 1) : d23494 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28775, d23494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28775, d23494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro70478 (p : Pattern) (ha : d236582 p = 1) (hb : d238880 p = 1) : d211168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d236582 q = 1) : d23406 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d23406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70465 q ha hb
    | true =>
      simp only [d16063, d23406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57510 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d236582 q = 1) : d23407 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d23407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d23407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d236582 q = 1) : d23408 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d23408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d23408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d236582 q = 1) : d23409 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d23409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d23409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d236582 q = 1) : d23416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d23416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70466 q ha hb
    | true =>
      simp only [d16070, d23416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57512 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d236582 q = 1) : d23417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d23417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d23417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d236582 q = 1) : d23418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d23418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d23418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28769 q = 1) (hb : d236582 q = 1) : d23440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28769, d23440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70472 q ha hb
    | true =>
      simp only [d28769, d23440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70460 q ha hb
  have h9 (q : Pattern) (ha : d236582 q = 1) (hb : d238871 q = 1) : d211159 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238871, d211159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d238871, d211159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d236582 q = 1) : d23477 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d23477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70467 q ha hb
    | true =>
      simp only [d16115, d23477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d236582 q = 1) : d23478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d23478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d23478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d236582 q = 1) (hb : d238872 q = 1) : d211160 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238872, d211160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238872, d211160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d236582 q = 1) (hb : d238873 q = 1) : d211161 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238873, d211161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d238873, d211161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d236582 q = 1) (hb : d238874 q = 1) : d211162 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238874, d211162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d238874, d211162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16122 q = 1) (hb : d236582 q = 1) : d23485 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16122, d23485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70474 q ha hb
    | true =>
      simp only [d16122, d23485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57520 q ha hb
  have h16 (q : Pattern) (ha : d16123 q = 1) (hb : d236582 q = 1) : d23486 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16123, d23486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16123, d23486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16124 q = 1) (hb : d236582 q = 1) : d23487 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16124, d23487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16124, d23487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16125 q = 1) (hb : d236582 q = 1) : d23488 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16125, d23488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16125, d23488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16127 q = 1) (hb : d236582 q = 1) : d23491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16127, d23491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70475 q ha hb
    | true =>
      simp only [d16127, d23491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57522 q ha hb
  have h20 (q : Pattern) (ha : d16128 q = 1) (hb : d236582 q = 1) : d23492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16128, d23492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16128, d23492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16129 q = 1) (hb : d236582 q = 1) : d23493 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16129, d23493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16129, d23493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d28776 q = 1) (hb : d236582 q = 1) : d23495 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28776, d23495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70477 q ha hb
    | true =>
      simp only [d28776, d23495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70462 q ha hb
  have h23 (q : Pattern) (ha : d236582 q = 1) (hb : d238876 q = 1) : d211164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238876, d211164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d238876, d211164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d16136 q = 1) (hb : d236582 q = 1) : d23501 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d23501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70476 q ha hb
    | true =>
      simp only [d16136, d23501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16137 q = 1) (hb : d236582 q = 1) : d23502 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d23502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16137, d23502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d236582 q = 1) (hb : d238877 q = 1) : d211165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238877, d211165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d238877, d211165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d236582 q = 1) (hb : d238878 q = 1) : d211166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238878, d211166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d238878, d211166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d236582 q = 1) (hb : d238879 q = 1) : d211167 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238879, d211167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d238879, d211167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d236582 q = 1) (hb : d238880 q = 1) : d211168 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238880, d211168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d238880, d211168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro70479 (p : Pattern) (ha : d236582 p = 1) (hb : d238887 p = 1) : d211175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28776 q = 1) (hb : d236582 q = 1) : d23495 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28776, d23495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70477 q ha hb
    | true =>
      simp only [d28776, d23495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70462 q ha hb
  have h2 (q : Pattern) (ha : d236582 q = 1) (hb : d238876 q = 1) : d211164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238876, d211164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238876, d211164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d16136 q = 1) (hb : d236582 q = 1) : d23501 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d23501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70476 q ha hb
    | true =>
      simp only [d16136, d23501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16137 q = 1) (hb : d236582 q = 1) : d23502 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d23502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16137, d23502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d236582 q = 1) (hb : d238877 q = 1) : d211165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238877, d211165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238877, d211165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d236582 q = 1) (hb : d238885 q = 1) : d211173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238885, d211173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238885, d211173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d236582 q = 1) (hb : d238886 q = 1) : d211174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238886, d211174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238886, d211174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d236582 q = 1) (hb : d238887 q = 1) : d211175 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238887, d211175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238887, d211175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70480 (p : Pattern) (ha : d16176 p = 1) (hb : d236582 p = 1) : d23550 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d236582 q = 1) : d23316 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d23316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70453 q ha hb
    | true =>
      simp only [d16005, d23316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57463 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d236582 q = 1) : d23317 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d23317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d23317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d236582 q = 1) : d23318 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d23318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d23318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d236582 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d236582 q = 1) : d23172 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d23172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57463 q ha hb
    | true =>
      simp only [d232, d23172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d236582 q = 1) : d23173 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d23173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d23173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d236582 q = 1) : d23174 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d23174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d23174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d236582 q = 1) : d23319 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d23319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d23319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d673 q = 1) (hb : d236582 q = 1) : d23548 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d23548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d673, d23548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16175 q = 1) (hb : d236582 q = 1) : d23549 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16175, d23549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16175, d23549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16176 q = 1) (hb : d236582 q = 1) : d23550 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16176, d23550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16176, d23550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro70481 (p : Pattern) (ha : d16186 p = 1) (hb : d236582 p = 1) : d23564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d236582 q = 1) : d23551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d23551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70480 q ha hb
    | true =>
      simp only [d16177, d23551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d236582 q = 1) : d23552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d23552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d23552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d236582 q = 1) : d23559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d23559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57506 q ha hb
    | true =>
      simp only [d684, d23559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d236582 q = 1) : d23560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d23560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d23560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16183 q = 1) (hb : d236582 q = 1) : d23561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16183, d23561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16183, d23561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16184 q = 1) (hb : d236582 q = 1) : d23562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16184, d23562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16184, d23562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16185 q = 1) (hb : d236582 q = 1) : d23563 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16185, d23563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16185, d23563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16186 q = 1) (hb : d236582 q = 1) : d23564 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16186, d23564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16186, d23564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro70482 (p : Pattern) (ha : d16207 p = 1) (hb : d236582 p = 1) : d23598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d236582 q = 1) : d23551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d23551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70480 q ha hb
    | true =>
      simp only [d16177, d23551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d236582 q = 1) : d23552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d23552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d23552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16204 q = 1) (hb : d236582 q = 1) : d23595 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16204, d23595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16204, d23595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16205 q = 1) (hb : d236582 q = 1) : d23596 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16205, d23596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16205, d23596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16206 q = 1) (hb : d236582 q = 1) : d23597 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16206, d23597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16206, d23597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16207 q = 1) (hb : d236582 q = 1) : d23598 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16207, d23598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16207, d23598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro70483 (p : Pattern) (ha : d28803 p = 1) (hb : d236582 p = 1) : d23539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28794 q = 1) (hb : d236582 q = 1) : d23534 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28794, d23534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28794, d23534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70468 q ha hb
  have h2 (q : Pattern) (ha : d28746 q = 1) (hb : d236582 q = 1) : d23422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70468 q ha hb
    | true =>
      simp only [d28746, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28795 q = 1) (hb : d236582 q = 1) : d23535 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28795, d23535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28795, d23535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28747 q = 1) (hb : d236582 q = 1) : d23423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28747, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28796 q = 1) (hb : d236582 q = 1) : d23536 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28796, d23536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28796, d23536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28797 q = 1) (hb : d236582 q = 1) : d23537 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28797, d23537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28797, d23537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28798 q = 1) (hb : d236582 q = 1) : d23310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28798, d23310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28798, d23310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70469 q ha hb
  have h8 (q : Pattern) (ha : d28751 q = 1) (hb : d236582 q = 1) : d23231 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28751, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70469 q ha hb
    | true =>
      simp only [d28751, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28799 q = 1) (hb : d236582 q = 1) : d23311 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28799, d23311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28799, d23311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28752 q = 1) (hb : d236582 q = 1) : d23232 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28752, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28752, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d28800 q = 1) (hb : d236582 q = 1) : d23312 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28800, d23312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28800, d23312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d28801 q = 1) (hb : d236582 q = 1) : d23313 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28801, d23313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d28801, d23313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d28802 q = 1) (hb : d236582 q = 1) : d23538 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28802, d23538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28802, d23538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d23314 q = 1) (hb : d236582 q = 1) : d23314 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d28803 q = 1) (hb : d236582 q = 1) : d23539 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28803, d23539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d28803, d23539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro70484 (p : Pattern) (ha : d28809 p = 1) (hb : d236582 p = 1) : d23545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28804 q = 1) (hb : d236582 q = 1) : d23540 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28804, d23540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70483 q ha hb
    | true =>
      simp only [d28804, d23540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70453 q ha hb
  have h2 (q : Pattern) (ha : d28805 q = 1) (hb : d236582 q = 1) : d23541 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28805, d23541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28805, d23541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28806 q = 1) (hb : d236582 q = 1) : d23542 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28806, d23542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28806, d23542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16166 q = 1) (hb : d236582 q = 1) : d16166 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16167 q = 1) (hb : d236582 q = 1) : d23316 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16167, d23316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70453 q ha hb
    | true =>
      simp only [d16167, d23316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16168 q = 1) (hb : d236582 q = 1) : d23317 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16168, d23317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16168, d23317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16169 q = 1) (hb : d236582 q = 1) : d23318 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16169, d23318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16169, d23318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28807 q = 1) (hb : d236582 q = 1) : d23543 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28807, d23543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28807, d23543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d16005 q = 1) (hb : d236582 q = 1) : d23316 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d23316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70453 q ha hb
    | true =>
      simp only [d16005, d23316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57463 q ha hb
  have h10 (q : Pattern) (ha : d16006 q = 1) (hb : d236582 q = 1) : d23317 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d23317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d23317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16007 q = 1) (hb : d236582 q = 1) : d23318 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d23318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d23318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d71 q = 1) (hb : d236582 q = 1) : d71 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d232 q = 1) (hb : d236582 q = 1) : d23172 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d23172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57463 q ha hb
    | true =>
      simp only [d232, d23172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d233 q = 1) (hb : d236582 q = 1) : d23173 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d23173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d23173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d234 q = 1) (hb : d236582 q = 1) : d23174 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d23174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d23174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16008 q = 1) (hb : d236582 q = 1) : d23319 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d23319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16008, d23319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28808 q = 1) (hb : d236582 q = 1) : d23544 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28808, d23544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28808, d23544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d28809 q = 1) (hb : d236582 q = 1) : d23545 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28809, d23545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d28809, d23545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h18 p ha hb
theorem andIntro70485 (p : Pattern) (ha : d28815 p = 1) (hb : d236582 p = 1) : d23556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28810 q = 1) (hb : d236582 q = 1) : d23546 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28810, d23546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70484 q ha hb
    | true =>
      simp only [d28810, d23546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28811 q = 1) (hb : d236582 q = 1) : d23547 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28811, d23547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28811, d23547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16177 q = 1) (hb : d236582 q = 1) : d23551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d23551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70480 q ha hb
    | true =>
      simp only [d16177, d23551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16178 q = 1) (hb : d236582 q = 1) : d23552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d23552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d23552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28812 q = 1) (hb : d236582 q = 1) : d23553 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28812, d23553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28812, d23553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28813 q = 1) (hb : d236582 q = 1) : d23554 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28813, d23554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28813, d23554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28814 q = 1) (hb : d236582 q = 1) : d23555 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28814, d23555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28814, d23555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28815 q = 1) (hb : d236582 q = 1) : d23556 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28815, d23556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28815, d23556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro70486 (p : Pattern) (ha : d236582 p = 1) (hb : d238897 p = 1) : d211185 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28816 q = 1) (hb : d236582 q = 1) : d23565 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28816, d23565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70485 q ha hb
    | true =>
      simp only [d28816, d23565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70481 q ha hb
  have h2 (q : Pattern) (ha : d236582 q = 1) (hb : d238893 q = 1) : d211181 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238893, d211181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238893, d211181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d16208 q = 1) (hb : d236582 q = 1) : d23599 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16208, d23599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70482 q ha hb
    | true =>
      simp only [d16208, d23599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16209 q = 1) (hb : d236582 q = 1) : d23600 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16209, d23600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16209, d23600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d236582 q = 1) (hb : d238894 q = 1) : d211182 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238894, d211182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238894, d211182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d236582 q = 1) (hb : d238895 q = 1) : d211183 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238895, d211183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238895, d211183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d236582 q = 1) (hb : d238896 q = 1) : d211184 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238896, d211184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238896, d211184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d236582 q = 1) (hb : d238897 q = 1) : d211185 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238897, d211185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238897, d211185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70487 (p : Pattern) (ha : d236582 p = 1) (hb : d238903 p = 1) : d211191 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16049 q = 1) (hb : d236582 q = 1) : d23389 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16049, d23389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16049, d23389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70461 q ha hb
  have h2 (q : Pattern) (ha : d16050 q = 1) (hb : d236582 q = 1) : d23390 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16050, d23390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16050, d23390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16058 q = 1) (hb : d236582 q = 1) : d23399 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, d23399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70461 q ha hb
    | true =>
      simp only [d16058, d23399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70463 q ha hb
  have h4 (q : Pattern) (ha : d16059 q = 1) (hb : d236582 q = 1) : d23400 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, d23400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16059, d23400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16060 q = 1) (hb : d236582 q = 1) : d23401 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16060, d23401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16060, d23401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236582 q = 1) (hb : d238881 q = 1) : d211169 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238881, d211169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70473 q ha hb
    | true =>
      simp only [d238881, d211169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70478 q ha hb
  have h7 (q : Pattern) (ha : d16144 q = 1) (hb : d236582 q = 1) : d23520 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16144, d23520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70464 q ha hb
    | true =>
      simp only [d16144, d23520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57504 q ha hb
  have h8 (q : Pattern) (ha : d236582 q = 1) (hb : d238882 q = 1) : d211170 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238882, d211170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d238882, d211170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d236582 q = 1) (hb : d238883 q = 1) : d211171 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238883, d211171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238883, d211171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d236582 q = 1) (hb : d238884 q = 1) : d211172 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238884, d211172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d238884, d211172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d236582 q = 1) (hb : d238888 q = 1) : d211176 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238888, d211176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238888, d211176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70479 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d236582 q = 1) : d23529 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d23529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d23529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57505 q ha hb
  have h13 (q : Pattern) (ha : d236582 q = 1) (hb : d238889 q = 1) : d211177 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238889, d211177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d238889, d211177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d236582 q = 1) (hb : d238890 q = 1) : d211178 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238890, d211178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238890, d211178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d236582 q = 1) (hb : d238891 q = 1) : d211179 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238891, d211179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d238891, d211179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d236582 q = 1) (hb : d238892 q = 1) : d211180 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238892, d211180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d238892, d211180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d236582 q = 1) (hb : d238898 q = 1) : d211186 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238898, d211186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238898, d211186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70486 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d236582 q = 1) : d23616 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d23616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d23616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57508 q ha hb
  have h19 (q : Pattern) (ha : d236582 q = 1) (hb : d238899 q = 1) : d211187 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238899, d211187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d238899, d211187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d236582 q = 1) (hb : d238900 q = 1) : d211188 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238900, d211188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d238900, d211188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d236582 q = 1) (hb : d238901 q = 1) : d211189 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238901, d211189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d238901, d211189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d236582 q = 1) (hb : d238902 q = 1) : d211190 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238902, d211190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d238902, d211190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d236582 q = 1) (hb : d238903 q = 1) : d211191 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d238903, d211191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d238903, d211191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro70488 (p : Pattern) (ha : d236582 p = 1) (hb : d238909 p = 1) : d211197 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236582 q = 1) (hb : d238904 q = 1) : d211192 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d238904, d211192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238904, d211192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70487 q ha hb
  have h2 (q : Pattern) (ha : d236582 q = 1) (hb : d238905 q = 1) : d211193 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d238905, d211193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238905, d211193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d236582 q = 1) (hb : d238906 q = 1) : d211194 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d238906, d211194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238906, d211194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d236582 q = 1) (hb : d238907 q = 1) : d211195 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d238907, d211195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238907, d211195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d236582 q = 1) (hb : d238908 q = 1) : d211196 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d238908, d211196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238908, d211196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236582 q = 1) (hb : d238909 q = 1) : d211197 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d238909, d211197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238909, d211197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70489 (p : Pattern) (ha : d28836 p = 1) (hb : d236582 p = 1) : d23630 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28746 q = 1) (hb : d236582 q = 1) : d23422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70468 q ha hb
    | true =>
      simp only [d28746, d23422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28747 q = 1) (hb : d236582 q = 1) : d23423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28747, d23423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28748 q = 1) (hb : d236582 q = 1) : d23424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28748, d23424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28748, d23424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28749 q = 1) (hb : d236582 q = 1) : d23425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28749, d23425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28749, d23425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28751 q = 1) (hb : d236582 q = 1) : d23231 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28751, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70469 q ha hb
    | true =>
      simp only [d28751, d23231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28752 q = 1) (hb : d236582 q = 1) : d23232 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28752, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28752, d23232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28753 q = 1) (hb : d236582 q = 1) : d23233 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28753, d23233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28753, d23233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28754 q = 1) (hb : d236582 q = 1) : d23234 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28754, d23234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28754, d23234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28755 q = 1) (hb : d236582 q = 1) : d23426 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28755, d23426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28755, d23426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23234 q = 1) (hb : d236582 q = 1) : d23234 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d751 q = 1) (hb : d236582 q = 1) : d5451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57536 q ha hb
    | true =>
      simp only [d751, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d752 q = 1) (hb : d236582 q = 1) : d5452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d752, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d753 q = 1) (hb : d236582 q = 1) : d5453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d5453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d5453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d754 q = 1) (hb : d236582 q = 1) : d5454 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d5454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d754, d5454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d28835 q = 1) (hb : d236582 q = 1) : d23629 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28835, d23629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28835, d23629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d28836 q = 1) (hb : d236582 q = 1) : d23630 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28836, d23630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28836, d23630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro70490 (p : Pattern) (ha : d28842 p = 1) (hb : d236582 p = 1) : d23641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28837 q = 1) (hb : d236582 q = 1) : d23632 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28837, d23632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70489 q ha hb
    | true =>
      simp only [d28837, d23632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57538 q ha hb
  have h2 (q : Pattern) (ha : d28838 q = 1) (hb : d236582 q = 1) : d23633 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28838, d23633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28838, d23633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28839 q = 1) (hb : d236582 q = 1) : d23634 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28839, d23634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28839, d23634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d763 q = 1) (hb : d236582 q = 1) : d23635 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d23635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57538 q ha hb
    | true =>
      simp only [d763, d23635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57539 q ha hb
  have h5 (q : Pattern) (ha : d764 q = 1) (hb : d236582 q = 1) : d23636 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d23636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d23636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d765 q = 1) (hb : d236582 q = 1) : d23637 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d23637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d23637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28840 q = 1) (hb : d236582 q = 1) : d23638 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28840, d23638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28840, d23638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d767 q = 1) (hb : d236582 q = 1) : d23639 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d23639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d767, d23639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28841 q = 1) (hb : d236582 q = 1) : d23640 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28841, d23640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28841, d23640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28842 q = 1) (hb : d236582 q = 1) : d23641 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28842, d23641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28842, d23641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro70491 (p : Pattern) (ha : d28848 p = 1) (hb : d236582 p = 1) : d23651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d236582 q = 1) : d23642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70490 q ha hb
    | true =>
      simp only [d28843, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d236582 q = 1) : d23643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d236582 q = 1) : d23646 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57541 q ha hb
    | true =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d236582 q = 1) : d23647 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d236582 q = 1) : d23648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d23648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d23648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28846 q = 1) (hb : d236582 q = 1) : d23649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28846, d23649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28846, d23649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28847 q = 1) (hb : d236582 q = 1) : d23650 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28847, d23650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28847, d23650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28848 q = 1) (hb : d236582 q = 1) : d23651 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28848, d23651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28848, d23651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70492 (p : Pattern) (ha : d28854 p = 1) (hb : d236582 p = 1) : d23661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28849 q = 1) (hb : d236582 q = 1) : d23656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28849, d23656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70491 q ha hb
    | true =>
      simp only [d28849, d23656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57543 q ha hb
  have h2 (q : Pattern) (ha : d28850 q = 1) (hb : d236582 q = 1) : d23657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28850, d23657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28850, d23657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28851 q = 1) (hb : d236582 q = 1) : d23658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28851, d23658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28851, d23658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28852 q = 1) (hb : d236582 q = 1) : d23659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28852, d23659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28852, d23659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28853 q = 1) (hb : d236582 q = 1) : d23660 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28853, d23660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28853, d23660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28854 q = 1) (hb : d236582 q = 1) : d23661 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28854, d23661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28854, d23661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro70493 (p : Pattern) (ha : d28857 p = 1) (hb : d236582 p = 1) : d23664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d236582 q = 1) : d23642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70490 q ha hb
    | true =>
      simp only [d28843, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d236582 q = 1) : d23643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d236582 q = 1) : d23646 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57541 q ha hb
    | true =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d236582 q = 1) : d23647 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d236582 q = 1) : d23648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d23648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d23648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28846 q = 1) (hb : d236582 q = 1) : d23649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28846, d23649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28846, d23649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28847 q = 1) (hb : d236582 q = 1) : d23650 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28847, d23650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28847, d23650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28857 q = 1) (hb : d236582 q = 1) : d23664 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28857, d23664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28857, d23664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro70494 (p : Pattern) (ha : d28863 p = 1) (hb : d236582 p = 1) : d23671 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28849 q = 1) (hb : d236582 q = 1) : d23656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28849, d23656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70491 q ha hb
    | true =>
      simp only [d28849, d23656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57543 q ha hb
  have h2 (q : Pattern) (ha : d28850 q = 1) (hb : d236582 q = 1) : d23657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28850, d23657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28850, d23657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28851 q = 1) (hb : d236582 q = 1) : d23658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28851, d23658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28851, d23658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28852 q = 1) (hb : d236582 q = 1) : d23659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28852, d23659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28852, d23659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28853 q = 1) (hb : d236582 q = 1) : d23660 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28853, d23660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28853, d23660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28858 q = 1) (hb : d236582 q = 1) : d23666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28858, d23666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70493 q ha hb
    | true =>
      simp only [d28858, d23666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57546 q ha hb
  have h7 (q : Pattern) (ha : d28859 q = 1) (hb : d236582 q = 1) : d23667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28859, d23667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28859, d23667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28860 q = 1) (hb : d236582 q = 1) : d23668 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28860, d23668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28860, d23668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28861 q = 1) (hb : d236582 q = 1) : d23669 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28861, d23669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28861, d23669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28862 q = 1) (hb : d236582 q = 1) : d23670 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28862, d23670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28862, d23670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28863 q = 1) (hb : d236582 q = 1) : d23671 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28863, d23671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28863, d23671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro70495 (p : Pattern) (ha : d28985 p = 1) (hb : d236582 p = 1) : d23793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28849 q = 1) (hb : d236582 q = 1) : d23656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28849, d23656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70491 q ha hb
    | true =>
      simp only [d28849, d23656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57543 q ha hb
  have h2 (q : Pattern) (ha : d28850 q = 1) (hb : d236582 q = 1) : d23657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28850, d23657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28850, d23657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28851 q = 1) (hb : d236582 q = 1) : d23658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28851, d23658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28851, d23658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28852 q = 1) (hb : d236582 q = 1) : d23659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28852, d23659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28852, d23659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28853 q = 1) (hb : d236582 q = 1) : d23660 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28853, d23660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28853, d23660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d236582 q = 1) : d23788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d23788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57543 q ha hb
    | true =>
      simp only [d939, d23788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d236582 q = 1) : d23789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d23789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d23789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d236582 q = 1) : d23790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d23790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d23790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d236582 q = 1) : d23791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d23791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d23791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d236582 q = 1) : d23792 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d23792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d23792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28985 q = 1) (hb : d236582 q = 1) : d23793 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28985, d23793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28985, d23793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro70496 (p : Pattern) (ha : d28868 p = 1) (hb : d236582 p = 1) : d23676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d236582 q = 1) : d23642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70490 q ha hb
    | true =>
      simp only [d28843, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d236582 q = 1) : d23643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d236582 q = 1) : d23646 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57541 q ha hb
    | true =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d236582 q = 1) : d23647 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d236582 q = 1) : d23648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d23648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d23648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28846 q = 1) (hb : d236582 q = 1) : d23649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28846, d23649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28846, d23649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28867 q = 1) (hb : d236582 q = 1) : d23675 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28867, d23675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28867, d23675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28868 q = 1) (hb : d236582 q = 1) : d23676 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28868, d23676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28868, d23676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70497 (p : Pattern) (ha : d28875 p = 1) (hb : d236582 p = 1) : d23685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d236582 q = 1) : d23642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70490 q ha hb
    | true =>
      simp only [d28843, d23642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d236582 q = 1) : d23643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d23643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d236582 q = 1) : d23646 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57541 q ha hb
    | true =>
      simp only [d774, d23646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d236582 q = 1) : d23647 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d23647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d236582 q = 1) : d23648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d23648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d23648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28873 q = 1) (hb : d236582 q = 1) : d23683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28873, d23683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28873, d23683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28874 q = 1) (hb : d236582 q = 1) : d23684 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28874, d23684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28874, d23684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28875 q = 1) (hb : d236582 q = 1) : d23685 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28875, d23685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28875, d23685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro70498 (p : Pattern) (ha : d28891 p = 1) (hb : d236582 p = 1) : d23694 p = 1 := by
  have h0 (q : Pattern) (ha : d824 q = 1) (hb : d236581 q = 1) : d824 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28885 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d28886 q = 1) (hb : d236582 q = 1) : d23692 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d28886, d236582, d23692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28886, d236582, d23692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d28887 q = 1) (hb : d236582 q = 1) : d23693 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28887, d23693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28887, d23693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d533 q = 1) (hb : d236581 q = 1) : d533 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d28888 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d28889 q = 1) (hb : d236582 q = 1) : d23419 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d28889, d236582, d23419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28889, d236582, d23419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d28890 q = 1) (hb : d236582 q = 1) : d23420 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28890, d23420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28890, d23420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d28891 q = 1) (hb : d236582 q = 1) : d23694 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28891, d23694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28891, d23694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro70499 (p : Pattern) (ha : d28896 p = 1) (hb : d236582 p = 1) : d23421 p = 1 := by
  have h0 (q : Pattern) (ha : d533 q = 1) (hb : d236581 q = 1) : d533 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28742 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d28743 q = 1) (hb : d236582 q = 1) : d23419 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d28743, d236582, d23419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28743, d236582, d23419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d236582 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d28744 q = 1) (hb : d236582 q = 1) : d23420 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28744, d23420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28744, d23420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23229 q = 1) (hb : d236582 q = 1) : d23229 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d28896 q = 1) (hb : d236582 q = 1) : d23421 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28896, d23421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28896, d23421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
